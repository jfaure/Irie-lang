{-# LANGUAGE LambdaCase, MultiWayIf, ScopedTypeVariables #-}
import CmdLine
import qualified ParseSyntax as P
import Parser
import CoreSyn
import ToCore
import TypeJudge

import Text.Megaparsec
import qualified Data.Text as T
import qualified Data.Text.IO as T.IO
import Control.Monad.Trans (lift)
import System.Console.Haskeline
import System.Exit

-- emitParseTree :: Bool
-- emitCore      :: Bool
-- emitStg       :: Bool
-- emitLlvm      :: Bool

-- jit           :: Bool
-- optlevel      :: Word
-- files         :: [String]

main = parseCmdLine >>= \cmdLine ->
  case files cmdLine of
    [] -> repl cmdLine
    av -> mapM_ (doFile cmdLine) av

doFile :: CmdLine -> FilePath -> IO ()
doFile c fName = T.IO.readFile fName >>= doProgText c fName

doProgText :: CmdLine -> FilePath -> T.Text -> IO ()
doProgText flags fName progText =
  let parseTree = case parseModule fName progText of
          Left e  -> (putStrLn $ errorBundlePretty e) *> pure []
          Right r -> pure r
      core   = parseTree2Core <$> parseTree
      judged = judgeModule <$> core
  in if
  | emitParseTree flags -> mapM_ print =<< parseTree
  | emitParseCore flags -> putStrLn . ppCoreModule =<< core
  | emitCore flags      -> print =<< judged
  | otherwise           -> putStrLn . ppCoreModule =<< judged

repl :: CmdLine -> IO ()
repl cmdLine = runInputT defaultSettings loop
 where 
  loop = getInputLine ">>= " >>= \case
    Nothing -> return ()
    Just l  -> lift doLine *> loop
      where doLine = print =<< doProgText cmdLine "<stdin>" (T.pack l)
