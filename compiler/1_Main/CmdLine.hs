module CmdLine (CmdLine(..), parseCmdLine, defaultCmdLine)
where

import Options.Applicative
import Data.Semigroup ((<>))
import qualified Data.Text as T

data CmdLine = CmdLine
  { printPass      :: T.Text


  , jit            :: Bool
  , optlevel       :: Word
  , noPrelude      :: Bool
  , outFile        :: Maybe String
  , files          :: [String]
  } deriving (Show)

printPasses = ["source", "parseTree", "preCore", "core", "stg", "llvm"] :: [T.Text]

parsePrintPass :: ReadM T.Text
parsePrintPass = eitherReader $ \str ->
  case filter (T.isInfixOf (T.pack str)) printPasses of
  []  -> Left $ "Unrecognized print pass: '" ++ str ++ "'"
  [p] -> Right p
  tooMany -> Left $ "Ambiguous print pass: '" ++ str ++ "'"

defaultCmdLine = CmdLine "" False 0 False Nothing []

cmdLineDecls :: Parser CmdLine
cmdLineDecls = CmdLine
  <$> option parsePrintPass
      (short 'p' <> long "print"
      <> help "print a pass"
      <> value "")
  <*> switch
      (short 'j' <> long "jit"
      <> help "Execute program in jit")
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

progDescription = "The Arya language is an array oriented calculus of inductive constructions for system level programming. This program is it's compiler/interpreter"
cmdLineInfo =
  let description = fullDesc
        <> header "Arya compiler/interpreter"
        <> progDesc progDescription
  in info (helper <*> cmdLineDecls) description

parseCmdLine :: IO CmdLine
parseCmdLine = execParser cmdLineInfo
