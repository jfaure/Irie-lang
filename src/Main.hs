{-# LANGUAGE LambdaCase #-}
import CmdLine
import ParseSyntax
import Parser
import ToCore

import Text.Megaparsec
import qualified Data.Text as T
import qualified Data.Text.IO as T.IO
import Control.Monad.Trans (lift)
import System.Console.Haskeline

main = parseCmdLine >>= \cmdLine ->
  case files cmdLine of
    [] -> repl cmdLine
    av -> mapM_ (doFile cmdLine) av

doFile :: CmdLine -> FilePath -> IO ()
doFile c fName = T.IO.readFile fName >>= doProgText c fName

parseProgText :: CmdLine -> FilePath -> T.Text -> IO ()
parseProgText c fName progText = case parseModule fName progText of
  Left e  -> putStrLn $ errorBundlePretty e
  Right r -> return r

doProgText :: CmdLine -> FilePath -> T.Text -> IO ()
doProgText flags fName progText =
  let parseTree = parseProgText flags fName progText
      core = parseTree2Core =<< parseTree
  in if
   | emitParseTree flags -> mapM_ print parseTree
   | otherwise -> print core

repl :: CmdLine -> IO ()
repl cmdLine = runInputT defaultSettings loop where 
  loop = getInputLine "bpc-jit> " >>= \case
          Nothing -> return ()
          Just l  -> lift (mapM_ print $ parseProgText cmdLine "<stdin>" (T.pack l))
                     *> loop
