-- main =~ Text >> Parse >> Core >> STG >> LLVM
import CmdLine
import ParseSyntax as P
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
import qualified LLVM.Exception as L

import Text.Megaparsec hiding (many)
import qualified Data.Text as T
import qualified Data.Text.IO as T.IO
import qualified Data.Text.Lazy.IO as TL.IO
import qualified Data.Vector as V
import qualified Data.Map as M
import Control.Monad.Trans (lift)
import Control.Applicative
import Control.Monad
import Control.Lens
import System.Console.Haskeline
import System.Exit
import System.IO (hFlush , stdout)
import Data.Functor
import Data.Function
import Data.Foldable
import Data.List
import Data.Maybe
import Debug.Trace

searchPath = ["./" , "Library/"]

main = parseCmdLine >>= initGlobalFlags >>= \cmdLine ->
  when ("args" `elem` printPass cmdLine) (print cmdLine)
  *> case files cmdLine of
    []  -> replCore cmdLine
    av  -> doFile cmdLine primResolver `mapM_` av
--  av  -> void $ loadParalelly cmdLine ([LoadedModule {coreBinds=primBinds}] , primResolver) av

doFile cmdLine it f = T.IO.readFile f >>= doProgText cmdLine it f
doProgText flags it f t = text2Core flags it f t >>= codegen flags

text2Core :: CmdLine -> GlobalResolver -> FilePath -> T.Text
  -> IO (GlobalResolver , Externs , JudgedModule)
text2Core flags resolver fName progText = do
  parsed <- case parseModule fName progText of
     Left e  -> (putStrLn $ errorBundlePretty e) *> die ""
     Right r -> pure r
  let modNameMap = parsed ^. parseDetails . hNameBinds . _2
      hNames = let getNm (FunBind nm _ _ _ _) = nm in getNm <$> V.fromList (_bindings parsed)

  importPaths <- (findModule searchPath . T.unpack) `mapM` (parsed ^. imports)
--(modResolver , localImports)
--  <- unzip . map (\(a,b,c)->a) <$> doFile flags resolver `mapM` importPaths
  modResolver <- foldM (\res path -> (\(a,b,c)->a) <$> doFile flags res path) resolver importPaths

  -- let-rec
  let (newResolver , exts) = resolveImports resolver (bind2Expr <$> judgedBinds) parsed
      judgedModule@(JudgedModule bindNames judgedBinds bis qtt argTys) = judgeModule parsed hNames exts
  let judged'    = V.zip bindNames judgedBinds
      namedBinds = (\(nm,j)->clYellow nm `T.append` T.pack (prettyBind j)) <$> judged'
      putPass :: T.Text -> IO () = \case
        "args"       -> print flags
        "source"     -> putStr =<< readFile fName
        "parseTree"  -> putStrLn $ prettyModule parsed
--      "core"       -> putStrLn $ show judged
        "core"       -> void $ T.IO.putStrLn `mapM` namedBinds
        "namedCore"  -> void $ T.IO.putStrLn `mapM` namedBinds
        _ -> pure ()
      addPass passNm = putStrLn "\n  ---  \n" *> putPass passNm
  putPass `mapM_` (printPass flags)
  pure (newResolver , exts , judgedModule)
--pure ((newResolver , Import modNameMap judged') , exts , judgedModule)

---------------------------------
-- Phase 2: codegen, linking, jit
---------------------------------
--codegen flags input@((resolver , Import bindNames judged) , exts , judgedModule) = let
codegen flags input@(resolver , exts , judgedModule) = let
  llvmMod    = mkStg exts judgedModule
  putPass :: T.Text -> IO () = \case
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
replWith :: forall a. a -> (a -> T.Text -> IO a) -> IO a
replWith startState fn = let
  doLine state = getInputLine "$ " >>= \case
    Nothing -> pure state
    Just l  -> lift (fn state (T.pack l)) >>= doLine
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
