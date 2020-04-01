{-# LANGUAGE OverloadedLists , OverloadedStrings #-}
import CmdLine
import ParseSyntax
import Parser
import Modules
import Externs
import CoreSyn
import qualified CoreUtils as CU
import PrettyCore
import Infer
import MkStg
--import Core2Stg
--import StgSyn
import StgToLLVM (stgToIRTop)
import qualified LlvmDriver as LD

import Text.Megaparsec
import qualified Data.Text as T
import qualified Data.Text.IO as T.IO
import qualified Data.Text.Lazy.IO as TL.IO

import Control.Monad.Trans (lift)
import Control.Applicative
import Control.Monad
import System.Console.Haskeline
import System.Exit
import Data.Functor
import Data.Maybe (isJust, fromJust)
import qualified Data.Vector as V
import LLVM.Pretty
import Debug.Trace

preludeFNames = V.empty -- V.fromList ["Library/Prim.arya"]
searchPath    = ["Library/"] :: [T.Text]

yoloPrependPrelude f = liftA2 T.append
  (T.IO.readFile "Library/Prim.arya") (T.IO.readFile f)

main = parseCmdLine >>= \cmdLine ->
  case files cmdLine of
    []  -> repl cmdLine
--  [f] -> doProgText cmdLine f =<< yoloPrependPrelude f
    [f] -> doProgText cmdLine f =<< T.IO.readFile f
    av  -> error "one file pls"
--  av -> mapM_ (doFile cmdLine) av

doProgText :: CmdLine -> FilePath -> T.Text -> IO ()
doProgText flags fName progText = do
  let preludes = if noPrelude flags then V.empty else preludeFNames
 
  parsed <- case parseModule fName progText of
     Left e  -> (putStrLn $ errorBundlePretty e) *> die ""
     Right r -> pure r
 -- inclPaths <- getModulePaths searchPath $ modImports pTree
 -- customImports <- mapM doImport inclPaths
 --   importList = autoImports V.++ customImports
 --   headers    = CU.mkHeader <$> importList
 --   llvmObjs   = V.toList $ stgToIRTop . core2stg <$> headers
  let pp         = printPass flags
      exts       = resolveImports parsed
      judged     = judgeModule parsed exts
      namedBinds = let
        mkNm (FunBind nm _ _) j = show nm ++ show j
        in zipWith mkNm (_bindings parsed) (V.toList judged)
      stg        = mkStg (extBinds exts) judged
      llvmMod    = stgToIRTop stg
      putPass    = \case
        "source"   -> putStr =<< readFile fName
        "parseTree"-> print parsed
        "core"     -> putStrLn $ show judged
        "namedCore"-> print $ foldl (\a b -> a++"\n"++b) "" namedBinds
        "stg"      -> print stg
        "llvm"     -> TL.IO.putStrLn $ ppllvm llvmMod
        _ -> putStrLn $ show judged --ppCoreModule judged
  putPass (printPass flags)
  putStrLn "\n  ---  \n" *> putPass "namedCore"
  putStrLn "\n  ---  \n" *> putPass "stg"
  putStrLn "\n  ---  \n" *> putPass "llvm"

-- | isJust (outFile flags) -> LD.writeFile (fromJust $ outFile flags) $ llvmMod
-- | pp == "stg"       -> putStrLn $ show stg
-- | pp == "llvm"      -> TL.IO.putStrLn $ ppllvm llvmMod
                            -- LD.dumpModule llvmMod
-- | jit flags -> LD.runJIT (optlevel flags) llvmObjs llvmMod

repl :: CmdLine -> IO ()
repl cmdLine = let
  doLine l = print =<< doProgText cmdLine "<stdin>" (T.pack l)
  loop     = getInputLine "'''" >>= \case
      Nothing -> pure ()
      Just l  -> lift (doLine l) *> loop
 in runInputT defaultSettings loop
