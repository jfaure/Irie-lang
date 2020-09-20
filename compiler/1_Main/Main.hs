-- main =~ Text >> Parse >> Core >> STG >> LLVM
import CmdLine
import GlobalFlags
import ParseSyntax
import Parser
import ModulePaths
import Externs
import CoreSyn
import PrettyCore
import Infer
import CodeGen
import LLVM.Pretty
import qualified LlvmDriver as LD
import qualified LLVM.Exception as L

import Text.Megaparsec
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
import Data.Maybe (isJust, fromJust)
import Debug.Trace

searchPath = ["./" , "Library/"]

main = parseCmdLine >>= initGlobalFlags >>= \cmdLine ->
  case files cmdLine of
    []  -> repl cmdLine
    av  -> doFile cmdLine M.empty `mapM_` av

repl :: CmdLine -> IO ()
repl cmdLine = let
  doLine l = doProgText cmdLine M.empty "<stdin>" (T.pack l)
    >>= print . importBinds . snd . fst
  loop     = getInputLine "'''" >>= \case
      Nothing -> pure ()
      Just l  -> lift (doLine l) *> loop
 in runInputT defaultSettings loop

doFile cmdLine it f = T.IO.readFile f >>= doProgText cmdLine it f
doProgText flags it f t = text2Core flags it f t >>= codegen flags

------------------------------------------------
-- Phase 1: parsing, resolve externs, type check
------------------------------------------------
text2Core :: CmdLine -> ImportTree -> FilePath -> T.Text
  -> IO ((ImportTree , Import) , Externs)
text2Core flags seenImports fName progText = do
  parsed <- case parseModule fName progText of
     Left e  -> (putStrLn $ errorBundlePretty e) *> die ""
     Right r -> pure r
  let modNameMap = parsed ^. parseDetails . hNameBinds . _2

  importPaths <- (findModule searchPath . T.unpack) `mapM` (parsed^.imports)
  (upTreeImports , localImports)
    <- unzip . map fst <$> doFile flags seenImports `mapM` importPaths

  let exts       = resolveImports localImports parsed
      judged     = judgeModule parsed exts
      bindNames  = let getNm (FunBind nm _ _ _ _) = nm
        in getNm <$> V.fromList (_bindings parsed)
      judged'    = V.zip bindNames judged
      namedBinds = (\(nm,j)->T.unpack nm ++ show j) <$> judged'
      putPass :: T.Text -> IO () = \case
        "args"       -> print flags
        "source"     -> putStr =<< readFile fName
        "parseTree"  -> print parsed
--      "core"       -> putStrLn $ show judged
        "core"       -> putStrLn $ V.foldl (\a b -> a++"\n"++b) "" namedBinds
        "namedCore"  -> putStrLn $ V.foldl (\a b -> a++"\n"++b) "" namedBinds
        _ -> pure ()
      addPass passNm = putStrLn "\n  ---  \n" *> putPass passNm
  putPass `mapM_` (printPass flags)
  pure ((_ , Import modNameMap judged') , exts)

---------------------------------
-- Phase 2: codegen, linking, jit
---------------------------------
codegen flags input@((imports , Import bindNames judged) , exts) = let
  llvmMod    = mkStg (extBinds exts) judged
  putPass :: T.Text -> IO () = \case
    "llvm-hs"    -> let
      text = ppllvm llvmMod
      in TL.IO.putStrLn text *> TL.IO.writeFile "/tmp/aryaOut.ll" text
    "llvm-cpp"   -> LD.dumpModule llvmMod
    _            -> pure ()
  in input <$ do
    putPass `mapM_` printPass flags
    when (jit flags) $ LD.runJIT (optlevel flags) [] llvmMod
