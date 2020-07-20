module CmdLine (CmdLine(..), parseCmdLine, defaultCmdLine)
where

import Options.Applicative
import qualified Data.Text as T

data CmdLine = CmdLine
  { printPass      :: [T.Text]
  , jit            :: Bool
  , optlevel       :: Word
  , noPrelude      :: Bool
  , outFile        :: Maybe String
  , files          :: [String]
  } deriving (Show)

defaultCmdLine = CmdLine [] False 0 False Nothing []

printPasses = ["source", "parseTree", "core", "stg", "llvm"] :: [T.Text]

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

progDescription = "The Nimzo language is an array oriented calculus of inductive constructions for system level programming. This program is it's compiler/interpreter"
cmdLineInfo =
  let description = fullDesc
        <> header "Nimzo compiler/interpreter"
        <> progDesc progDescription
  in info (helper <*> cmdLineDecls) description

parseCmdLine :: IO CmdLine
-- parseCmdLine = execParser cmdLineInfo
parseCmdLine = customExecParser (prefs disambiguate) cmdLineInfo
