-- Command line arguments are very nearly global constants
--  they must be initialized first thing at runtime
module CmdLine (CmdLine(..), parseCmdLine, defaultCmdLine) where
import Options.Applicative
import Data.Text as T

data CmdLine = CmdLine
  { printPass      :: [Text]
  , jit            :: Bool
  , debug          :: Bool
  , optlevel       :: Word
  , noPrelude      :: Bool
  , outFile        :: Maybe FilePath
  , files          :: [FilePath]
  } deriving (Show)

defaultCmdLine = CmdLine [] False False 0 False Nothing []

printPasses = T.words "args source parseTree types core simple ssa C" :: [Text]

parsePrintPass :: ReadM [Text]
parsePrintPass = eitherReader $ \str -> let
  passesStr = split (==',') (toS str)
  checkAmbiguous s = case Prelude.filter (isInfixOf s) printPasses of
    []  -> Left $ "Unrecognized print pass: '" ++ str ++ "'"
    [p] -> Right p
    tooMany -> Left $ "Ambiguous print pass: '" ++ str ++ "' : " ++ show tooMany
  in sequence (checkAmbiguous <$> passesStr)

cmdLineDecls :: Parser CmdLine
cmdLineDecls = CmdLine
  <$> (option parsePrintPass)
      (short 'p' <> long "print"
      <> help (toS $ "print compiler pass(es separated by ',') : [" <> T.intercalate " | " printPasses <> "]")
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
      <> help "Write llvm output to file")
  <*> many (argument str (metavar "FILE"))

progDescription = "Compiler and Interpreter for the Irie language, a subtyping CoC for system level programming."
cmdLineInfo =
  let description = fullDesc
        <> header "Irie compiler/interpreter"
        <> progDesc progDescription
  in info (helper <*> cmdLineDecls) description

-- parseCmdLine :: IO CmdLine
-- parseCmdLine = execParser cmdLineInfo
-- parseCmdLine = customExecParser (prefs disambiguate) cmdLineInfo
parseCmdLine :: [String] -> IO CmdLine
 = \rawArgs -> handleParseResult
   $ execParserPure (prefs disambiguate) cmdLineInfo rawArgs
