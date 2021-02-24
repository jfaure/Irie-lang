-- Command line arguments are very nearly global constants
--  they must be initialized first thing at runtime
module CmdLine (CmdLine(..), parseCmdLine, defaultCmdLine
      , initGlobalFlags , getGlobalFlags)
where
import Options.Applicative
import qualified Data.Text as T
import Data.IORef
import System.IO.Unsafe

globalFlags :: IORef CmdLine
  = unsafePerformIO $ newIORef defaultCmdLine
initGlobalFlags :: CmdLine -> IO CmdLine -- call this once, at startup
  = \flags -> flags <$ writeIORef globalFlags flags
getGlobalFlags :: CmdLine
  = unsafePerformIO $ readIORef globalFlags

data CmdLine = CmdLine
  { printPass      :: [T.Text]
  , jit            :: Bool
  , debug          :: Bool
  , optlevel       :: Word
  , noPrelude      :: Bool
  , outFile        :: Maybe FilePath
  , files          :: [FilePath]
  } deriving (Show)

defaultCmdLine = CmdLine [] False False 0 False Nothing []

printPasses = ["args" , "source", "parseTree", "core", "llvm-hs" , "llvm-cpp"] :: [T.Text]

parsePrintPass :: ReadM [T.Text]
parsePrintPass = eitherReader $ \str -> let
  passesStr = T.split (==',') (T.pack str)
  checkAmbiguous s = case filter (T.isInfixOf s) printPasses of
    []  -> Left $ "Unrecognized print pass: '" ++ str ++ "'"
    [p] -> Right p
    tooMany -> Left $ "Ambiguous print pass: '" ++ str ++ "' : " ++ show tooMany
  in sequence (checkAmbiguous <$> passesStr)

cmdLineDecls :: Parser CmdLine
cmdLineDecls = CmdLine
  <$> (option parsePrintPass)
      (short 'p' <> long "print"
      <> help "print a pass: source|parseTree|preCore|core|stg|llvm"
      <> value [])
  <*> switch
      (short 'j' <> long "jit"
      <> help "Execute program in jit")
  <*> switch
      (short 'd' <> long "debug"
      <> help "Print information with maximum verbosity")
  <*> option auto
      (short 'O'
      <> help "Optimization level [0..3]"
      <> value 0)
  <*> switch
      (short 'n' <> long "no-prelude"
      <> help "don't import prelude implicitly")
  <*> (optional . strOption) (
      (short 'o')
      <> help "Write output to file")
  <*> many (argument str (metavar "FILE"))

progDescription = "Compiler and Interpreter for the Nimzo language, an array oriented calculus of inductive constructions for system level programming."
cmdLineInfo =
  let description = fullDesc
        <> header "Nimzo compiler/interpreter"
        <> progDesc progDescription
  in info (helper <*> cmdLineDecls) description

-- parseCmdLine :: IO CmdLine
-- parseCmdLine = execParser cmdLineInfo
-- parseCmdLine = customExecParser (prefs disambiguate) cmdLineInfo
parseCmdLine :: [String] -> IO CmdLine
 = \rawArgs -> handleParseResult
   $ execParserPure (prefs disambiguate) cmdLineInfo rawArgs
