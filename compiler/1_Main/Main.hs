module Main where
import CmdLine
import Registry (Registry , initRegistry , compileFiles , g_noCache)
import qualified Data.List (words)
import System.Console.Repline
--import System.Process (callCommand)

-- <dead code> for use in ghci
demoFile   = "demo.ii"
sh         = main' . Data.List.words
[parseTree , ssa , core , types , opt , emitC , interp] = sh . (demoFile <>) <$>
  [" -p parse" , " -p ssa" , " -p core", " -p types" , " -p simple" , " -p C" , " --interpret"]
testRepl   = sh ""

main = getArgs >>= main'
main' args = do
  cmdLine <- parseCmdLine args
  reg     <- initRegistry (g_noCache || noCache cmdLine)
  compileFiles cmdLine reg (files cmdLine)
  when (repl cmdLine || null (files cmdLine)) (runRepl cmdLine reg)

type Repl = HaskelineT (StateT CmdLine IO)

-- Commands
-- repl Cmds
-- show set unset { add browse cd cmd complete def doc edit info help load main reload type script undef paste ..debugging
-- deps
replOpts :: [(String , String -> Repl ())]
replOpts = 
  [ ("help" , \s -> liftIO $ putStrLn ("Help: " <> s))
  , ("load" , \s -> liftIO $ readFile s >>= putStrLn)
--, ("set"  , \s -> case s of
--    "put-core" -> .= True
--  )
  ] -- callCommand

defaultMatcher :: MonadIO m => [([Char], CompletionFunc m)]
defaultMatcher = let
  helpCompleter :: Monad m => WordCompleter m
  helpCompleter n = pure (filter (isPrefixOf n) (fst <$> replOpts))
  in 
  [ (":load", fileCompleter)
  , (":help", wordCompleter helpCompleter)
  ]

optCompleter :: Monad m => WordCompleter m
optCompleter n = pure (filter (isPrefixOf n) ((':' :) . fst <$> replOpts))

mkPrompt :: MultiLine -> Repl String
mkPrompt = \case { SingleLine -> pure ">>> " ; MultiLine -> pure "| " }

evalLine :: String -> Repl ()
evalLine = liftIO . print

runRepl :: CmdLine -> Registry -> IO ()
runRepl cmd reg = void $ (`evalStateT` cmd) $ evalReplOpts ReplOpts
  { banner = mkPrompt
  , command = evalLine
  , options = replOpts
  , prefix = Just ':'
  , multilineCommand = Just "paste"
  , tabComplete = (Prefix (wordCompleter optCompleter) defaultMatcher)
  , initialiser = pure ()
  , finaliser = pure Exit 
  }
