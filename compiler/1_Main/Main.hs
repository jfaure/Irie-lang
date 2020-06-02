{-# LANGUAGE OverloadedLists , OverloadedStrings #-}
import CmdLine
import ParseSyntax
import Parser
import ModulePaths
import Externs
import CoreSyn
import PrettyCore
import Infer
import MkStg
--import Core2Stg
--import StgSyn
import StgToLLVM (stgToIRTop)
import qualified LlvmDriver as LD
import LLVM.Pretty

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
import Data.Functor
import Data.Maybe (isJust, fromJust)
import Debug.Trace

preludeFNames = V.empty -- V.fromList ["Library/Prim.arya"]
searchPath    = ["" , "Library/"]

main = parseCmdLine >>= \cmdLine ->
  case files cmdLine of
    []  -> repl cmdLine
    [f] -> void $ doFile cmdLine M.empty f
    av  -> error "one file pls"
--  av -> mapM_ (doFile cmdLine) av

doFile cmdLine it f = doProgText cmdLine it f =<< T.IO.readFile f

doProgText :: CmdLine -> ImportTree -> FilePath -> T.Text
  -> IO (ImportTree , Import)
doProgText flags seenImports fName progText = do
  parsed <- case parseModule fName progText of
     Left e  -> (putStrLn $ errorBundlePretty e) *> die ""
     Right r -> pure r
  let modNameMap = parsed ^. parseDetails . hNameBinds . _2

  importPaths
    <- (findModule searchPath . T.unpack) `mapM` (parsed^.imports)
  (upTreeImports , localImports)
    <- unzip <$> doFile flags seenImports `mapM` importPaths

  let exts       = resolveImports localImports parsed
      judged     = judgeModule parsed exts
      bindNames  = let getNm (FunBind nm _ _ _) = nm
        in getNm <$> V.fromList (_bindings parsed)
      namedBinds = V.zipWith (\nm j -> show nm ++ show j) bindNames judged
      stg        = mkStg (extBinds exts) (V.zip bindNames judged)
      llvmMod    = stgToIRTop stg
      putPass :: T.Text -> IO ()   = \case
        "source"     -> putStr =<< readFile fName
        "parseTree"  -> print parsed
        "core"       -> putStrLn $ show judged
        "namedCore"  -> putStrLn $ V.foldl (\a b -> a++"\n"++b) "" namedBinds
        _ -> putStrLn $ show judged --ppCoreModule judged
      addPass passNm = putStrLn "\n  ---  \n" *> putPass passNm
  putPass (printPass flags)
  addPass "namedCore"
  pure (_ , Import modNameMap judged)

--      "stg"        -> print stg
--      "llvm"       -> TL.IO.putStrLn $ ppllvm llvmMod
--      "llvm-print" -> LD.dumpModule llvmMod
--      "jit"        -> LD.runJIT (optlevel flags) [] llvmMod

repl :: CmdLine -> IO ()
repl cmdLine = let
  doLine l = print.importBinds.snd =<< doProgText cmdLine M.empty "<stdin>" (T.pack l)
  loop     = getInputLine "'''" >>= \case
      Nothing -> pure ()
      Just l  -> lift (doLine l) *> loop
 in runInputT defaultSettings loop
