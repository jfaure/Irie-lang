{-# Language TemplateHaskell #-}
module Main where
import CmdLine
import Externs
import Registry (initRegistry , compileFiles , g_noCache , compileText)
import qualified Data.List (words)
import qualified Data.Text as T
import System.Console.Repline
import Control.Lens
--import System.Process (callCommand)

data ReplState = ReplState { _replCmdLine :: CmdLine , _replRegistry :: Registry }; makeLenses ''ReplState
type Repl = HaskelineT (StateT ReplState IO)

-- <dead code> for use in ghci
demoFile   = "demo.ii"
sh         = main' . Data.List.words
[parseTree , ssa , core , types , opt , emitC , interp] = sh . (demoFile <>) <$>
  [" -p parse" , " -p ssa" , " -p core", " -p types" , " -p simple" , " -p C" , " --interpret"]
testRepl   = sh ""

main = getArgs >>= main'
main' = parseCmdLine >=> \cmdLine -> do
  reg <- initRegistry (g_noCache || noCache cmdLine)
  compileFiles cmdLine reg (files cmdLine)
  when (repl cmdLine || null (files cmdLine)) (runRepl cmdLine reg)

-- Commands
-- repl Cmds
-- show: binds imports linker modules packages paths language targets settings lang breaks context
-- set unset
-- add / reload / load (load deloads everything else)
-- browse
-- cd
-- cmd def undef
-- complete
-- doc
-- edit
-- info
-- help
-- main
-- type
-- script
-- debugging
-- deps

evalLine :: String -> Repl ()
evalLine txt = use replCmdLine >>= \c -> use replRegistry >>= \reg ->
  liftIO (void $ compileText c reg (T.pack txt))

replOpts :: [(String , String -> Repl ())]
replOpts = 
  [ ("help" , \s -> liftIO $ putStrLn ("Help: " <> s))
--, ("load" , \s -> liftIO $ readFile s >>= putStrLn)
--, ("set"  , \s -> case s of
--    "put-core" -> .= True
--  )
  ] -- callCommand

mkTabComplete = let
  cmdArgMatcher :: MonadIO m => [([Char], CompletionFunc m)]
  cmdArgMatcher = let
    helpCompleter :: Monad m => WordCompleter m
    helpCompleter n = pure (filter (isPrefixOf n) (fst <$> replOpts))
    in 
    [ (":load", fileCompleter)
    , (":help", wordCompleter helpCompleter)
    ]
  optCompleter :: Monad m => WordCompleter m
  optCompleter n = pure (filter (isPrefixOf n) ((':' :) . fst <$> replOpts))
  in Prefix (wordCompleter optCompleter) cmdArgMatcher

runRepl :: CmdLine -> Registry -> IO ()
runRepl rawCmdLine reg = let cmdLine = rawCmdLine { printPass = "simple" : printPass rawCmdLine }
  in void $ (`evalStateT` ReplState cmdLine reg) $ evalReplOpts ReplOpts
  { banner = \case { SingleLine -> pure "$> " ; MultiLine -> pure "|  " }
  , command = evalLine
  , options = replOpts
  , prefix = Just ':'
  , multilineCommand = Just "paste"
  , tabComplete = mkTabComplete
  , initialiser = pure ()
  , finaliser = pure Exit 
  }
