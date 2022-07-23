{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS -threaded -rtsopts -with-rtsopts=-N #-}
module Tests where
import Main
import CmdLine
import Externs

import qualified Data.Vector as V
import qualified Data.Text as T
import qualified Data.Text.IO as T.IO
import qualified Data.Text.Lazy as L
import System.IO.Unsafe
import Text.RawString.QQ
import qualified Test.Syd as S
import qualified GHC.Show

inferType :: Text -> L.Text
inferType s = let (_ , _ , _ , _ , _ , _ , _ , _ , (oTypes , _ , _)) = handleJudgedModule (unsafePerformIO $ text2Core defaultCmdLine{noColor = True , printPass = ["types"] , noCache = True} Nothing primResolver 0 "testExpr" s)
  in fromMaybe "" $ (V.! 0) <$> oTypes

newtype UniText = UniText L.Text deriving Eq
instance Show UniText where show (UniText l) = toS l

fTests = readTestsFromfile "imports/simpleTests.ii"
recTests = readTestsFromfile "imports/recTests.ii"
 
readTestsFromfile fName = let
  ls = filter (/= "") (T.lines (unsafePerformIO (T.IO.readFile fName)))
    <&> ((\(e,eT) -> (e , T.dropAround (== ' ') (T.drop 2 eT))) . T.breakOn "--")
  in filter (("" /=) . fst) ls <&> \(expr , expectedType) -> let
    name = T.takeWhile (/= ' ') expr
    in S.it (toS expr <> " -- " <> toS expectedType) (UniText (inferType expr) `S.shouldBe` UniText (toS (name <> " = " <> expectedType <> "\n")))

s = S.sydTest $ sequence_ fTests *> do
  let e :: Text = [r|
printList l = case l of
  Nil => 2
  Cons i ll => add (putNumber i) (printList ll)
    |] in S.describe "printList" $ S.it (toS e) $ UniText (inferType e)
      `S.shouldBe` UniText "printList = µx.[Nil | Cons {%i32 , x}] → (%i32 & %i32)\n"

  let e :: Text = [r|
-- need Nil and Cons in scope
unfoldr f b0 = case f b0 of
  Just ({ val as a , seed as b1 }) => Cons a (unfoldr f b1)
  Nothing       => Nil
null x = case x of
  Nil => 1
  Cons => 0
    |]
      in S.describe "unfoldr" $ S.it (toS e) $ UniText (inferType e)
        `S.shouldBe` UniText "unfoldr = ∏ A B → (A → [Just {{val : B , seed : A}} | Nothing]) → A → µx.[Nil | Cons {B , x}]\n"

  let e :: Text = [r|
filter pred l = case l of
  Nil => Nil
  Cons x xs => ifThenElse (pred x) (Cons x (filter pred xs)) (filter pred xs)
    |]
      in S.describe "filter" $ S.it (toS e) $ UniText (inferType e)
        `S.shouldBe` UniText "filter = ∏ A → (A → %i1) → µx.[Nil | Cons {A , x}] → µy.[Nil | Cons {A , y}]\n"
