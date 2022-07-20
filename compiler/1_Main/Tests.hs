{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS -threaded -rtsopts -with-rtsopts=-N #-}
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
import qualified Data.Text.Lazy as L
import System.IO.Unsafe

import Test.Tasty
import Test.Tasty.HUnit
import Text.RawString.QQ
import qualified Test.Syd as S

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

fileTests = let
  ls = filter (/= "") (T.lines (unsafePerformIO (T.IO.readFile "imports/simpleTests.ii")))
    <&> ((\(e,eT) -> (e , T.dropAround (== ' ') (T.drop 2 eT))) . T.breakOn "--")
  in filter (("" /=) . fst) ls <&> \(expr , expectedType) -> let
    name = T.takeWhile (/= ' ') expr
    in testCase (toS expr) (inferType expr @?= toS (name <> " = " <> expectedType <> "\n"))

ts = doTests

t = defaultMain tests
tests :: TestTree
tests = testGroup "Type inference tests" [ testGroup "one-liners" fileTests , unitTests ]

inferType :: Text -> L.Text
inferType s = let (_ , _ , _ , _ , _ , _ , _ , _ , (oTypes , _ , _)) = handleJudgedModule (unsafePerformIO $ text2Core defaultCmdLine{noColor = True , printPass = ["types"]} Nothing primResolver 0 "testExpr" s)
  in fromMaybe "" $ (V.! 0) <$> oTypes

unitTests :: TestTree
unitTests = testGroup "Lists"
  [ testCase "printList" $ (inferType [r|
printList l = case l of
  Nil => 2
  Cons i ll => add (putNumber i) (printList ll)
  |])
  @?= "printList = µx.[Nil | Cons {%i32 , x}] → (%i32 & %i32)\n"

-- , testCase "scanSum" $ inferType "scanSum n l = ifThenElse (le n 0) l (scanSum (sub n 1) (Cons n l))"
-- @?= "printList = µx.[Nil | Cons {%i32 , x}] → (%i32 & %i32)\n"
  ]

fTests = let
  ls = filter (/= "") (T.lines (unsafePerformIO (T.IO.readFile "imports/simpleTests.ii")))
    <&> ((\(e,eT) -> (e , T.dropAround (== ' ') (T.drop 2 eT))) . T.breakOn "--")
  in filter (("" /=) . fst) ls <&> \(expr , expectedType) -> let
    name = T.takeWhile (/= ' ') expr
    in S.it (toS expr <> " -- " <> toS expectedType) (inferType expr @?= toS (name <> " = " <> expectedType <> "\n"))

spec :: S.Spec
spec = let
  expr :: Text = [r|
printList l = case l of
  Nil => 2
  Cons i ll => add (putNumber i) (printList ll)
  |]
  in S.describe "printList" $ S.it (toS expr) $ inferType expr == "printList = µx.[Nil | Cons {%i32 , x}] → (%i32 & %i32)\n"

s = S.sydTest $ sequence_ fTests
