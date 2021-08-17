-- main = Text >> Parse >> Core >> STG >> LLVM
import CmdLine
import qualified ParseSyntax as P
import Parser
import ModulePaths
import Externs
import CoreSyn
import CoreUtils (bind2Expr)
import PrettyCore
import Infer
import CodeGen
import LLVM.Pretty
import qualified LlvmDriver as LD

import Text.Megaparsec hiding (many)
import qualified Data.Text.IO as T.IO
import qualified Data.Text.Lazy.IO as TL.IO
import qualified Data.Vector as V
import Control.Lens
import System.Console.Haskeline
import Data.List (words)

searchPath = ["./" , "Library/"]

main = getArgs >>= main'
sh   = main' . Data.List.words -- simplest way to pass cmdline args in ghci

main' args = parseCmdLine args >>= \cmdLine -> -- initGlobalFlags >>= \cmdLine ->
  when ("args" `elem` printPass cmdLine) (print cmdLine)
  *> case files cmdLine of
    []  -> replCore cmdLine
    av  -> doFile cmdLine primResolver `mapM_` av

doFile cmdLine it f = T.IO.readFile f >>= doProgText cmdLine it f
doProgText flags it f t = text2Core flags it f t >>= codegen flags

text2Core :: CmdLine -> GlobalResolver -> FilePath -> Text
  -> IO (GlobalResolver , Externs , JudgedModule)
text2Core flags resolver fName progText = do
  parsed <- case parseModule fName progText of
    Left e  -> (putStrLn $ errorBundlePretty e) *> die ""
    Right r -> pure r
  let modNameMap = parsed ^. P.parseDetails . P.hNameBinds . _2
      hNames = let getNm (P.FunBind fnDef) = P.fnNm fnDef in getNm <$> V.fromList (parsed ^. P.bindings)

  importPaths <- (findModule searchPath . toS) `mapM` (parsed ^. P.imports)
--(modResolver , localImports) <- unzip . map (\(a,b,c)->a) <$> doFile flags resolver `mapM` importPaths
  modResolver <- foldM (\res path -> (\(a,b,c)->a) <$> doFile flags res path) resolver importPaths

  -- let-rec on judgedBinds
  let localNames   = parsed ^. P.parseDetails . P.hNameBinds . _2
      mixfixNames  = parsed ^. P.parseDetails . P.hNameMFWords . _2
      unknownNames = parsed ^. P.parseDetails . P.hNamesNoScope
      labelNames   = iMap2Vector $ parsed ^. P.parseDetails . P.labels
      fieldNames   = iMap2Vector $ parsed ^. P.parseDetails . P.fields

--    (tmpResolver , exts) = resolveImports resolver localNames mixfixNames unknownNames
      (tmpResolver , exts) = resolveImports modResolver localNames mixfixNames unknownNames
      judgedModule@(JudgedModule bindNames judgedBinds) = judgeModule parsed hNames exts
      newResolver = addModule2Resolver tmpResolver (bind2Expr <$> judgedBinds)

  let judged'    = V.zip bindNames judgedBinds
      namedBinds = (\(nm,j)->clYellow nm <> toS (prettyBind False (BindSource _ bindNames _ labelNames fieldNames) j)) <$> judged'
      putPass :: Text -> IO () = \case
        "args"       -> print flags
        "source"     -> putStr =<< readFile fName
        "parseTree"  -> putStrLn $ P.prettyModule parsed
        "core"       -> void $ T.IO.putStrLn `mapM` namedBinds
        "namedCore"  -> void $ T.IO.putStrLn `mapM` namedBinds
        _ -> pure ()
      addPass passNm = putStrLn ("\n  ---  \n" :: Text) *> putPass passNm
  putPass `mapM_` (printPass flags)
  pure (newResolver , exts , judgedModule)

---------------------------------
-- Phase 2: codegen, linking, jit
---------------------------------
--codegen flags input@((resolver , Import bindNames judged) , exts , judgedModule) = let
codegen flags input@(resolver , exts , judgedModule) = let
  llvmMod    = mkStg exts judgedModule
  putPass :: Text -> IO () = \case
    "llvm-hs"    -> let
      text = ppllvm llvmMod
      in TL.IO.putStrLn text *> TL.IO.writeFile "/tmp/aryaOut.ll" text
    "llvm-cpp"   -> LD.dumpModule llvmMod
    _            -> pure ()
  in input <$ do
    putPass `mapM_` printPass flags
    when (jit flags) $ LD.runJIT (optlevel flags) [] llvmMod

----------
-- Repl --
----------
replWith :: forall a. a -> (a -> Text -> IO a) -> IO a
replWith startState fn = let
  doLine state = getInputLine "$ " >>= \case
    Nothing -> pure state
    Just l  -> lift (fn state (toS l)) >>= doLine
  in runInputT defaultSettings $ doLine startState

replCore :: CmdLine -> IO ()
replCore cmdLine = let
  doLine l = doProgText cmdLine primResolver "<stdin>" l >>= print . V.last . allBinds . (\(a,b,c) -> a)
  in void $ replWith cmdLine $ \cmdLine line -> cmdLine <$ doLine line

--replJIT :: CmdLine -> IO ()
--replJIT cmdLine = LD.withJITMachine $
--  \jit -> void $ replWith (cmdLine , jit) $
--  \state@(cmdLine , jit) l -> do
--    judged@((_,Import _ j),exts,jm) <- doProgText cmdLine primResolver "<stdin>" l
--    print $ importBinds $ snd $ (\(a,b,c)->a) judged
--    let llMod = mkStg exts (fst<$>j) jm
--    LD.runINJIT jit (Just (llMod , "test" , \_ -> pure ()))
--    pure state

repl2 = mapM T.IO.putStrLn =<< replWith [] (\st line -> pure $! line : st)

testrepl = replCore defaultCmdLine

testjit = LD.testJIT
