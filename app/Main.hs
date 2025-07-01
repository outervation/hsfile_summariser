{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Main (main) where

import Control.Monad
import Control.Monad.State.Strict
import Data.Generics.Uniplate.Data -- generic traversal
import Data.Set qualified as S
import GHC (ParsedSource, runGhc)
import GHC.Data.FastString (fsLit)
import GHC.Hs
import GHC.Hs.Binds ()
import GHC.Hs.Expr ()
import GHC.Hs.Extension ()
import GHC.Parser ()
import GHC.Parser.Annotation ()
import GHC.Parser.Lexer ()
import GHC.Paths (libdir)
import GHC.Types.Name.Reader (RdrName, mkVarUnqual)
import GHC.Types.SrcLoc
  ( GenLocated (..),
    RealSrcSpan,
    SrcSpan (..),
    combineSrcSpans,
    isGoodSrcSpan,
    noSrcSpan,
  )
import GHC.Utils.Outputable (ppr, showSDocUnsafe)
import GHC.Utils.Panic (panic)
import Language.Haskell.GHC.ExactPrint (exactPrint)
import Language.Haskell.GHC.ExactPrint.Parsers
import Language.Haskell.Syntax.Expr ()
import Language.Haskell.Syntax.Extension ()
import System.Environment (getArgs)
import System.Exit (die)

-- | RHS/source-location information we want to blank out
type BodySpans = S.Set RealSrcSpan

----------------------------------------------------------------------
-- 0  CLI helpers (unchanged)
----------------------------------------------------------------------

getOneArg :: IO FilePath
getOneArg =
  getArgs >>= \case
    [p] -> pure p
    _ -> die "Usage: hsfile-summariser <file.hs>"

(|>) :: a -> (a -> b) -> b
(|>) = flip ($)

----------------------------------------------------------------------
-- 1  Parse the module (with comments kept)
----------------------------------------------------------------------

assertRealSpan :: SrcSpan -> RealSrcSpan
assertRealSpan x = case x of
  RealSrcSpan sp _ -> sp
  UnhelpfulSpan _ -> undefined

lgrhssSpan :: LGRHS GhcPs (LHsExpr GhcPs) -> SrcSpan
lgrhssSpan lgrhs = getHasLoc lgrhs

-- A robust helper to combine a list of SrcSpans into one.
-- It handles empty lists and invalid spans gracefully.
combineSpans :: [SrcSpan] -> SrcSpan
combineSpans spans =
  case filter isGoodSrcSpan spans of
    [] -> noSrcSpan
    (s : ss) -> foldl' combineSrcSpans s ss

getLocalBindsLocation :: HsLocalBinds GhcPs -> SrcSpan
getLocalBindsLocation (HsValBinds _ (ValBinds _ binds sigs)) =
  let bind_spans = map getHasLoc binds
      sig_spans = map getHasLoc sigs
   in combineSpans (bind_spans ++ sig_spans)
getLocalBindsLocation (HsIPBinds _ (IPBinds _ ip_binds)) =
  combineSpans (map getHasLoc ip_binds)
getLocalBindsLocation (EmptyLocalBinds _) = noSrcSpan
-- This pattern is required to make the function total.
-- However, the parser should never produce an XValBindsLR.
-- We panic, as this indicates a severe logic error or a
-- misunderstanding of the GHC AST.
getLocalBindsLocation (HsValBinds _ (XValBindsLR {})) =
  panic "getLocalBindsLocation: Unexpected XValBindsLR in parsed source"

-- The function to get the location of the entire GRHSs block.
grhssSpan' :: GRHSs GhcPs (LHsExpr GhcPs) -> SrcSpan
grhssSpan' (GRHSs {..}) =
  -- Get the spans of all the individual guarded expressions.
  let grhs_spans = map lgrhssSpan grhssGRHSs

      -- Get the span of the 'where' clause.
      binds_span = getLocalBindsLocation grhssLocalBinds
   in -- Combine them all into a single span.
      combineSpans (binds_span : grhs_spans)

grhssSpan :: GRHSs GhcPs (LHsExpr GhcPs) -> RealSrcSpan
grhssSpan x = assertRealSpan $ grhssSpan' x

----------------------------------------------------------------------
-- 2  Traverse & strip
----------------------------------------------------------------------

stripModule ::
  GHC.ParsedSource -> State BodySpans GHC.ParsedSource
stripModule = transformBiM stripBind

stripBind ::
  LHsDecl GhcPs ->
  State BodySpans (LHsDecl GhcPs)
stripBind (L l (ValD ext bind)) =
  case bind of
    -- Note: we pattern match to get all fields of FunBind
    f@FunBind {..} -> do
      mg' <- stripMatchGroup fun_matches
      -- Reconstruct the FunBind explicitly. This is safe and total.
      let new_bind = f {fun_matches = mg'}
      pure $ L l (ValD ext new_bind)

    -- And we do the same for PatBind
    p@PatBind {..} -> do
      let rhs0 = pat_rhs
      rhs' <- blankGRHSs rhs0
      modify (S.insert (grhssSpan rhs0))
      -- Reconstruct the PatBind explicitly.
      let new_bind = p {pat_rhs = rhs'}
      pure $ L l (ValD ext new_bind)

    -- Other bind types are left alone
    _ -> pure (L l (ValD ext bind))
stripBind d = pure d -- type sigs etc.

-- | Replace every GRHS list with a single ‘<<hidden>>’ expression
stripMatchGroup ::
  MatchGroup GhcPs (LHsExpr GhcPs) ->
  State BodySpans (MatchGroup GhcPs (LHsExpr GhcPs))
stripMatchGroup mg@(MG {mg_alts = L _ alts}) = do
  alts' <- forM alts $ \(L l m) -> do
    rhs' <- blankGRHSs (m_grhss m)
    pure (L l m {m_grhss = rhs'})
  pure mg {mg_alts = noLocA alts'}

blankGRHSs ::
  GRHSs GhcPs (LHsExpr GhcPs) ->
  State BodySpans (GRHSs GhcPs (LHsExpr GhcPs))
blankGRHSs grhss = do
  -- remember span of the body for comment filtering
  modify (S.insert (grhssSpan grhss))
  let lhs = noLocA $ HsVar noExtField (noLocA identHidden)
      gr = noLocA $ GRHS noAnn [] lhs
  pure
    grhss
      { grhssGRHSs = [gr], -- replace bodies
        grhssLocalBinds = GHC.Hs.emptyLocalBinds
      }

identHidden :: RdrName
identHidden = mkVarUnqual (fsLit " = <<hidden>>")

----------------------------------------------------------------------
-- 4  Pretty-print & post-process
----------------------------------------------------------------------
main :: IO ()
main = do
  file <- getOneArg

  -- 'runGhc' initializes a GHC session and executes a Ghc monad action,
  -- returning the result into the IO monad.
  parsed0 <- runGhc (Just libdir) $ do
    r <- liftIO $ parseModule libdir file
    case r of
      Left errs -> liftIO $ die (showSDocUnsafe $ ppr errs)
      Right ps -> pure ps

  -- Once runGhc is complete, we are back in the IO monad with the results.
  let (parsed, _) = runState (stripModule parsed0) S.empty
      result =
        exactPrint parsed
          |> condenseBlanks
  putStrLn result

condenseBlanks :: String -> String
condenseBlanks = unlines . go . lines
  where
    go (a : b : rest) | all null [a, b] = go ("" : rest)
    go (x : rest) = x : go rest
    go [] = []
