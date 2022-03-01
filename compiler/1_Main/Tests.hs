module Tests where
import Main
import CmdLine
import CoreSyn
import PrettyCore
import Externs

import qualified Data.Vector as V
import qualified Data.Text as T
--import qualified Data.Text.Lazy.IO as TL.IO
import qualified Data.Text.IO as T.IO

-- Messy because it copies part of handleJudgedModule which otherwise prints everything instead of returning Text
-- TODO use updated handleJudgedModule
runTest (expr , expectedType)  = let
  -- a bit of a hack to get the raw types as Text before they are printed
  getType expr = text2Core defaultCmdLine{noColor = True} Nothing primResolver 0 "testExpr" (toS expr)
    <&> \(flags , fName , judgedModule , newResolver , _exts , errors , srcInfo) -> let
    JudgedModule modIName modNm nArgs bindNames a b judgedBinds = judgedModule
    nameBinds showTerm bs = let
      prettyBind' = prettyBind ansiRender { bindSource = Just bindSrc , ansiColor = False }
      in (\(nm,j) -> (prettyBind' showTerm nm j)) <$> bs
    bindNamePairs = V.zip bindNames judgedBinds
    bindSrc = BindSource _ bindNames _ (labelHNames newResolver) (fieldHNames newResolver) (allBinds newResolver)
    in V.foldr (<>) "" (nameBinds False bindNamePairs)
  nm = T.takeWhile (/= ' ') expr
  in getType expr <&> toS <&> \t -> let
    inferred = (T.takeWhile (/= '\n') $ T.drop 2 (T.dropWhile (/= '=') t))
    in if inferred /= expectedType
       then Just (nm <> " KO: " <> inferred <> " /= " <> expectedType) else Nothing

doTests = T.IO.readFile "imports/simpleTests.ii" <&> T.lines <&> filter (/= "")
  <&> map ((\(e,eT) -> (e , T.dropAround (== ' ') (T.drop 2 eT))) . T.breakOn "--")
  <&> filter (("" /=) . fst) >>= \lines -> do
  results <- catMaybes <$> lines `forM` runTest
  T.IO.putStrLn `mapM_` results
  let (nTests , ok) = (length lines , nTests - length results)
  T.IO.putStrLn $ show ok <> " / " <> show nTests <> " one-line tests"

ts = doTests
