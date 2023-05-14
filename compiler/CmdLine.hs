-- Command line arguments
module CmdLine (CmdLine(..) , parseCmdLine, defaultCmdLine) where
import Options.Applicative
import qualified Data.Text as T ( words, isInfixOf, intercalate, split )

data CmdLine = CmdLine
  { printPass      :: [Text]
  , interpret      :: Bool
  , jit            :: Bool
  , noColor        :: Bool
  , repl           :: Bool
  , optlevel       :: Word
  , threads        :: Int
  , noPrelude      :: Bool
  , noFuse         :: Bool
  , noCache        :: Bool
--  , reportErrors   :: Bool -- print an error summary (not doing so is probably only useful for the test suite)
  , recompile      :: Bool   -- recompile even if cached
  , quiet          :: Bool
  , outFile        :: Maybe FilePath
  , strings        :: String -- work on text from the commandline (as opposed to reading it from a file)
--  , searchPath     :: [String]
--  , objDirName     :: String
--  , objPath        :: [String]
  , files          :: [FilePath]
  } deriving (Show)

defaultObjDirName = ".irie-obj/"
defaultCmdLine = CmdLine -- Intended for use from ghci
  { printPass      = []
  , interpret      = False
  , jit            = False
  , noColor        = True
  , repl           = False
  , optlevel       = 0
  , threads        = 1
  , noPrelude      = False
  , noFuse         = False
  , noCache        = False
  , recompile      = False
  , quiet          = False
  , outFile        = Nothing
  , strings        = []
--  , searchPath     = ["./" , "ii/"]
--  , objDirName     = defaultObjDirName
--  , objPath        = ["./"]
  , files          = []
  }

printPasses = T.words "args source parseTree types core simple ssa C" :: [Text]

parsePrintPass :: ReadM [Text]
parsePrintPass = eitherReader $ \str -> let
  passesStr = T.split (==',') (toS str)
  checkAmbiguous s = case Prelude.filter (T.isInfixOf s) printPasses of
    []  -> Left $ "Unrecognized print pass: '" <> str <> "'"
    [p] -> Right p
    tooMany -> Left $ "Ambiguous print pass: '" <> str <> "' : " <> show tooMany
  in sequence (checkAmbiguous <$> passesStr)

cmdLineDecls :: Parser CmdLine
cmdLineDecls = CmdLine
  <$> (option parsePrintPass)
      (short 'p' <> long "print"
      <> help (toS $ "list of compiler passes to print (separated by ',') : [" <> T.intercalate " | " printPasses <> "]")
      <> value [])
  <*> switch
      (short 'i' <> long "interpret"
      <> help "Execute 'main' binding in haskell interpreter")
  <*> switch
      (short 'j' <> long "jit"
      <> help "Execute 'main' binding in jit")
  <*> switch
      (short 'N' <> long "no-color"
      <> help "Don't print ANSI color codes")
  <*> switch
      (short 'r' <> long "repl"
      <> help "Interactive read-eval-print loop")
  <*> option auto
      (short 'O'
      <> help "Optimization level 0|1|2|3"
      <> value 0)
  <*> option auto
      (short 't' <> long "threads"
      <> help "Number of threads >0 to run concurrently (should use far less RAM than forking the compiler on each file)"
      <> value 1)
  <*> switch
      (short 'n' <> long "no-prelude"
      <> help "Don't import prelude implicitly")
  <*> switch
      (             long "no-fuse"
      <> help "Don't perform fusion")
  <*> switch
      (             long "no-cache"
      <> help "Don't save or re-use compiled files")
  <*> switch
      (             long "recompile"
      <> help "recompile even if cached file looks good")
  <*> switch
      (             long "quiet"
      <> help "print less to stdout")
--  <*> ((\x->[x]) . strOption) (
--      (long "search-path")
--      <> help "Search path for irie modules")
--  <*> strOption (
--      long "obj-dir-name"
--      <> help "Dir to use for irie compilation artefacts")
--      <> _value defaultObjDirName
  <*> (optional . strOption) (
      (short 'o')
      <> help "Write output to FILE")
  <*> (strOption
      (short 'e' <> long "expression"
      <> metavar "STRING"
      <> help "Add the binding to the 'CmdLineBindings' module"
      <> value ""))
  <*> many (argument str (metavar "FILE"))

progDescription = "Compiler and Interpreter for the Irie language, a subtyping CoC for system level programming."
cmdLineInfo =
  let description = fullDesc
        <> header "Irie compiler/interpreter"
        <> progDesc progDescription
  in info (helper <*> cmdLineDecls) description

parseCmdLine :: [String] -> IO CmdLine
 = \rawArgs -> handleParseResult $ execParserPure (prefs disambiguate) cmdLineInfo rawArgs
