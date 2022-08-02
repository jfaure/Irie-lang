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
import System.Directory
import System.Process as SP
import System.IO.Temp (getCanonicalTemporaryDirectory)
import System.FilePath
import qualified System.IO as SIO
import Text.RawString.QQ
import qualified Test.Syd as S
import qualified GHC.Show

inferTypes s = let
  cmdLine = defaultCmdLine {noColor = True , printPass = ["types"] , noCache = True}
  (_ , _ , _ , _ , _ , _ , _ , _ , (oTypes , _ , _))
    = handleJudgedModule (unsafePerformIO $ text2Core cmdLine Nothing primResolver 0 "testExpr" s)
  in oTypes
inferType :: Text -> L.Text
inferType s = fromMaybe "" $ (V.! 0) <$> (inferTypes s)

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

caseTests = do
  let e :: Text = [r|
printList l = case l of
  Nil => 2
  Cons i ll => add (putNumber i) (printList ll)
|] in S.describe "printList" $ S.it (toS e) $ UniText (inferType e)
      `S.shouldBe` UniText "printList = ∏ A → µa.[Nil | Cons {%i32 , a}] → %i32\n"

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
        `S.shouldBe` UniText "unfoldr = ∏ A B C → (A → [Just {{val : B , seed : A}} | Nothing]) → A → µc.[Nil | Cons {B , c}]\n"

  let e :: Text = [r|
filter pred l = case l of
  Nil => Nil
  Cons x xs => ifThenElse (pred x) (Cons x (filter pred xs)) (filter pred xs)
|]
      in S.describe "filter" $ S.it (toS e) $ UniText (inferType e)
        `S.shouldBe` UniText "filter = ∏ A B C → (A → %i1) → µb.[Nil | Cons {A , b}] → µc.[Nil | Cons {A , c}]\n"

  let e :: Text = [r|
mergeRec = \case
  N => { x = 1 }
  C => { y = 1 }
|]
      in S.describe "mergeRecords" $ S.it (toS e) $ UniText (inferType e)
        `S.shouldBe` UniText "mergeRec = [N | C] → {}\n"


testImports = do
  (fp1 , h1) <- SIO.openTempFile "/tmp/" "m1"
  hPutStr h1 $ ("f = 3" :: Text)
  SIO.hClose h1

  (fp2 , h2) <- SIO.openTempFile "/tmp/" "m2"
  hPutStr h2 $ unlines ["import " <> toS fp1 , "g = f"]
  SIO.hClose h2
  Main.sh (fp2 <> " -p types")

testPhantomLabel = do
  _ <- SP.system "mv .irie-obj/* /tmp/"
  (fp1 , h1) <- SIO.openTempFile "/tmp/" "m1"
  hPutStr h1 $ T.unlines ["lol (Cons x xs) = x" , "g = Cons"]
  SIO.hClose h1
  Main.sh (fp1 <> " -p types")
  removeFile fp1
  h1 <- SIO.openFile fp1 WriteMode
  hPutStr h1 $ ("gg = Cons" :: Text)
  SIO.hClose h1
  Main.sh (fp1 <> " -p types")

tI = S.sydTest $ do
  S.runIO testPhantomLabel

--goldenList = S.goldenTextFile "golden/goldenList" $
--  withSystemTempFile "goldenList" $ \tmpFile tmpHandle -> do
--    Main.sh ("imports/list.ii -p types --no-fuse -o" <> tmpFile)
--    readFile tmpFile

goldenList fName goldName = S.goldenTextFile goldName $ do
   tmpFile <- (</> "goldenList") <$> getCanonicalTemporaryDirectory
   Main.sh (fName <> " -p types --no-fuse -o" <> tmpFile)
   readFile tmpFile

gold   = S.it "list.ii"   (goldenList "imports/list.ii"   "golden/goldenList")
mutual = S.it "mutual.ii" (goldenList "imports/sumMul.ii" "golden/sumMul")

g = S.sydTest gold
s = S.sydTest $ do
  sequence_ fTests
  --sequence_ recTests
  caseTests
  gold
  mutual
