{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RecordWildCards #-}

module Main (main) where

import           Control.Monad.State.Strict
import           Control.Monad (forM_)
import qualified Data.Set                    as S
import           Language.Haskell.Exts
import           System.Environment          (getArgs)
import           System.Exit                 (die)

type BodySpans = S.Set SrcSpan   -- collected RHS locations

--------------------------------------------------------------------------------
main :: IO ()
--------------------------------------------------------------------------------
main = do
  file <- getOneArg
  let pm = defaultParseMode { parseFilename = file
                            , extensions    = Language.Haskell.Exts.glasgowExts
                            }

  (m0, cs0) <- parseFileWithComments pm file >>= \case
                 ParseOk r       -> pure r
                 ParseFailed l e -> die $ prettyPrint l <> ": " <> e

  let (mStripped, spans) = runState (stripModule m0) S.empty
      csStripped         = filter (not . insideAny spans) cs0

      result = exactPrint mStripped csStripped
                 -- compress 3+ consecutive blank lines to one:
                 |> condenseBlanks

  putStrLn result
 where (|>) = flip ($)

--------------------------------------------------------------------------------
-- 1.  erase function / pattern bodies
--------------------------------------------------------------------------------
stripModule :: Module SrcSpanInfo -> State BodySpans (Module SrcSpanInfo)
stripModule (Module l mh ps imps decls) =
  Module l mh ps imps <$> mapM stripDecl decls
stripModule m = pure m

stripDecl :: Decl SrcSpanInfo -> State BodySpans (Decl SrcSpanInfo)
stripDecl = \case
  FunBind l ms          -> FunBind l <$> mapM stripMatch ms

  --  remember the ‘where’ span (if present) and remove it
  PatBind l pat rhs mbinds -> do
      rhs' <- stripRhs rhs
      forM_ mbinds $ \b -> modify (S.insert $ srcInfoSpan (ann b))
      pure $ PatBind l pat rhs' Nothing

  d                     -> pure d

stripMatch :: Match SrcSpanInfo -> State BodySpans (Match SrcSpanInfo)
stripMatch = \case
  Match l n ps rhs mbinds -> do
      rhs' <- stripRhs rhs
      forM_ mbinds $ \b -> modify (S.insert $ srcInfoSpan (ann b))
      pure $ Match l n ps rhs' Nothing

  InfixMatch l pat n ps rhs mbinds -> do
      rhs' <- stripRhs rhs
      forM_ mbinds $ \b -> modify (S.insert $ srcInfoSpan (ann b))
      pure $ InfixMatch l pat n ps rhs' Nothing

stripRhs :: Rhs SrcSpanInfo -> State BodySpans (Rhs SrcSpanInfo)
stripRhs rhs = do
  modify (S.insert $ srcInfoSpan (ann rhs))
  let u = Var (ann rhs)
              (UnQual (ann rhs) (Ident (ann rhs) " <<hidden>>"))
  pure (UnGuardedRhs (ann rhs) u)

--------------------------------------------------------------------------------
-- 2.  comment-filtering helpers
--------------------------------------------------------------------------------
insideAny :: BodySpans -> Comment -> Bool
insideAny set (Comment _ sp _) = any (`contains` sp) set

-- More permissive containment: column comparisons only matter
-- on lines that coincide with the boundary of the outer span.
contains :: SrcSpan -> SrcSpan -> Bool
contains o i =
  sameFile
  && startOk
  && endOk
 where
  sameFile = srcSpanFilename o == srcSpanFilename i

  startOk
    | sl_i == sl_o = sc_i >= sc_o
    | otherwise    = sl_i  > sl_o

  endOk
    | el_i == el_o = ec_i <= ec_o
    | otherwise    = el_i  < el_o

  (sl_o, sc_o, el_o, ec_o) = loc o
  (sl_i, sc_i, el_i, ec_i) = loc i
  loc s = (srcSpanStartLine s, srcSpanStartColumn s
          ,srcSpanEndLine   s, srcSpanEndColumn   s)

--------------------------------------------------------------------------------
-- 3.  cosmetic: squeeze multiple blank lines
--------------------------------------------------------------------------------
condenseBlanks :: String -> String
condenseBlanks = unlines . go . lines
 where
  go (a:b:rest)
     | all null [a,b] = go ("" : rest)   -- drop extra empties
     | otherwise      = a : go (b:rest)
  go xs = xs

--------------------------------------------------------------------------------
-- 4.  misc
--------------------------------------------------------------------------------
getOneArg :: IO FilePath
getOneArg = getArgs >>= \case
  [p] -> pure p
  _   -> die "Usage: hsfile-summariser <path/to/File.hs>"
