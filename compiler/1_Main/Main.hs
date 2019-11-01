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
import Control.Monad.Trans (lift)
import System.Console.Haskeline
import System.Exit

main = parseCmdLine >>= \cmdLine ->
  case files cmdLine of
    [] -> repl cmdLine
    av -> mapM_ (doFile cmdLine) av

prelude = ["Library/Prim.stg"]

-- TODO modules
doFile :: CmdLine -> FilePath -> IO ()
doFile c fName = do
  preludes <- mapM T.IO.readFile prelude
  let prelude = if noPrelude c
                then T.empty
                else foldr T.append T.empty preludes :: T.Text
  f <- T.IO.readFile fName
  doProgText c fName (T.append prelude f)

doProgText :: CmdLine -> FilePath -> T.Text -> IO ()
doProgText flags fName progText =
  case parseModule fName progText of
          Left e  -> (putStrLn $ errorBundlePretty e) *> die ""
          Right r -> pure r
  >>= \parseTree ->
  let core      = parseTree2Core parseTree
      judged    = judgeModule core
      stg       = core2stg judged
      llvmMod   = stgToIRTop stg
  in if
  | emitSourceFile flags -> putStr =<< readFile fName
  | emitParseTree  flags -> mapM_ print parseTree
  | emitParseCore  flags -> putStrLn $ ppCoreModule core
  | emitCore       flags -> putStrLn $ ppCoreModule judged
  | emitStg        flags -> putStrLn $ show stg
  | emitLlvm       flags -> LD.dumpModule llvmMod
  | jit            flags -> LD.runJIT (optlevel flags) llvmMod
  | otherwise            -> putStrLn $ ppCoreModule judged -- ppCoreBinds judged

repl :: CmdLine -> IO ()
repl cmdLine = runInputT defaultSettings loop
 where 
  loop = getInputLine "<\"" >>= \case
    Nothing -> return ()
    Just l  -> lift doLine *> loop
      where doLine = print =<< doProgText cmdLine "<stdin>" (T.pack l)
