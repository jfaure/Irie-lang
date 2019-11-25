import CmdLine
--import qualified ParseSyntax as P
import CoreSyn
--import StgSyn
import Parser
import ToCore
import PrettyCore
import TypeJudge
import Core2Stg
import StgToLLVM (stgToIRTop)
import qualified LlvmDriver as LD

import Text.Megaparsec
import qualified Data.Text as T
import qualified Data.Text.IO as T.IO
import qualified Data.Text.Lazy.IO as TL.IO

import Control.Monad.Trans (lift)
import System.Console.Haskeline
import System.Exit
import Data.Functor
import Data.Maybe (isJust, fromJust)
import LLVM.Pretty

main = parseCmdLine >>= \cmdLine ->
  case files cmdLine of
    [] -> repl cmdLine
    [f] -> doProgText cmdLine f =<< T.IO.readFile f
    av -> error "one file pls"
--  av -> mapM_ (doFile cmdLine) av

preludeFNames = ["Library/Prim.stg"]

doImport :: FilePath -> T.Text -> IO CoreModule
doImport fName progText =
--putStrLn ("Compiling " ++ show fName) *>
  case parseModule fName progText of
    Left e  -> (putStrLn $ errorBundlePretty e) *> die ""
    Right r -> pure r
  <&> (judgeModule . parseTree2Core [])

doProgText :: CmdLine -> FilePath -> T.Text -> IO ()
doProgText flags fName progText = do
 imports   <- if noPrelude flags
   then pure []
   else mapM (\x -> doImport x =<< T.IO.readFile x) preludeFNames
-- putStrLn ("Compiling " ++ show fName)
 parseTree <- case parseModule fName progText of
         Left e  -> (putStrLn $ errorBundlePretty e) *> die ""
         Right r -> pure r
 let core      = parseTree2Core imports parseTree
     judged    = judgeModule core
     stg       = core2stg judged
     llvmMod   = stgToIRTop stg
 if
  | isJust (outFile flags) -> LD.writeFile (fromJust $ outFile flags) llvmMod
  | emitSourceFile flags -> putStr =<< readFile fName
  | emitParseTree  flags -> print parseTree
  | emitParseCore  flags -> putStrLn $ ppCoreModule core
  | emitCore       flags -> putStrLn $ ppCoreModule judged
  | emitStg        flags -> putStrLn $ show stg
  | emitLlvm       flags -> TL.IO.putStrLn $ ppllvm llvmMod -- LD.dumpModule llvmMod
  | jit            flags -> LD.runJIT (optlevel flags) llvmMod
  | otherwise            -> putStrLn $ ppCoreModule judged -- ppCoreBinds judged

repl :: CmdLine -> IO ()
repl cmdLine = runInputT defaultSettings loop
 where 
  loop = getInputLine "<\"" >>= \case
    Nothing -> return ()
    Just l  -> lift doLine *> loop
      where doLine = print =<< doProgText cmdLine "<stdin>" (T.pack l)
