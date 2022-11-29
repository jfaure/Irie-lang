{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS -threaded -rtsopts -with-rtsopts=-N #-}
module Tests where
import Main
import CmdLine
import Externs
import PrettyCore
import CoreSyn(BindSource(..))
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
  getResult (_flags , _coreOK , _errors , _srcInfo , _fName , r , j) =
    let bindSrc = BindSource mempty mempty mempty (labelHNames r) (allBinds r)
    in prettyJudgedModule False ansiRender {bindSource = Just bindSrc , ansiColor = False} j
  in unsafePerformIO $ getResult . Main.simplifyModule <$> text2Core cmdLine Nothing primResolver 0 "testExpr" s

--inferType ∷ Text → L.Text
--inferType s = fromMaybe "" $ (V.! 0) <$> (inferTypes s)
inferType = toS . inferTypes

newtype UniText = UniText L.Text deriving Eq
instance Show UniText where show (UniText l) = toS l

fTests = readTestsFromfile "imports/simpleTests.ii"
recTests = readTestsFromfile "imports/recTests.ii"

readTestsFromfile fName = let
  ls = filter (/= "") (T.lines (unsafePerformIO (T.IO.readFile fName)))
    <&> ((\(e,eT) → (e , T.dropAround (== ' ') (T.drop 2 eT))) . T.breakOn "--")
  in filter (("" /=) . fst) ls <&> \(expr , expectedType) → let
    name = T.takeWhile (/= ' ') expr
    in S.it (toS expr <> " -- " <> toS expectedType)
      (UniText (inferType expr) `S.shouldBe` UniText (toS (name <> " = " <> expectedType)))

caseTests = do
  let e ∷ Text = [r|
printList l = case l of
  @Nil ⇒ 2
  @Cons i ll ⇒ add (putNumber i) (printList ll)
|] in S.describe "printList" $ S.it (toS e) $ UniText (inferType e)
      `S.shouldBe` UniText "printList = ∏ A → µa.[Nil | Cons {%i32 , a}] → %i32"

-- val as a pattern no longer parsed
--   let e ∷ Text = [r|
-- -- need Nil and Cons in scope
-- unfoldr f b0 = case f b0 of
--   @Just ({ val as a , seed as b1 }) => @Cons a (unfoldr f b1)
--   @Nothing       => @Nil
-- null x = case x of
--   @Nil  => 1
--   @Cons => 0
-- |]
--       in S.describe "unfoldr" $ S.it (toS e) $ UniText (inferType e)
--         `S.shouldBe` UniText "unfoldr = ∏ A B C → (A → [Just {{val : B , seed : A}} | Nothing]) → A → µc.[Nil | Cons {B , c}]\n"

  let e ∷ Text = [r|
filter pred l = case l of
  @Nil ⇒ Nil
  @Cons x xs ⇒ ifThenElseInt1 (pred x) (Cons x (filter pred xs)) (filter pred xs)
 |]
      in S.describe "filter" $ S.it (toS e) $ UniText (inferType e)
        `S.shouldBe` UniText "filter = ∏ A B C → (A → %i1) → µb.[Nil | Cons {A , b}] → µc.[Nil | Cons {A , c}]"

  let e ∷ Text = [r|
mergeRec = \case
  @N ⇒ { x = 1 }
  @C ⇒ { y = 1 }
|]
      in S.describe "mergeRecords" $ S.it (toS e) $ UniText (inferType e)
        `S.shouldBe` UniText "mergeRec = [N | C] → {}"

  let e ∷ Text = [r|
import imports/prelude
testParity n = let
  isEven n = ifThenElse (eq n 0) 1 (isOdd  (sub n 1))
  isOdd  n = ifThenElse (eq n 0) 0 (isEven (sub n 1))
  in isEven n
|]
      in S.describe "let-mutuals" $ S.it (toS e) $ UniText (inferType e)
        `S.shouldBe` UniText "testParity = %i32 → %i1"

testImports = do
  (fp1 , h1) ← SIO.openTempFile "/tmp/" "m1"
  hPutStr h1 $ ("f = 3" ∷ Text)
  SIO.hClose h1

  (fp2 , h2) ← SIO.openTempFile "/tmp/" "m2"
  hPutStr h2 $ unlines ["import " <> toS fp1 , "g = f"]
  SIO.hClose h2
  Main.sh (fp2 <> " -p types")

testPhantomLabel = S.goldenTextFile (goldDir <> "phantomLabel") $ do
  _ ← SP.system "mv .irie-obj/* /tmp/"
  (fp1 , h1) ← SIO.openTempFile "/tmp/" "m1"
  hPutStr h1 $ T.unlines ["lol (MyLabel x xs) = x"]
  SIO.hClose h1
  Main.sh (fp1 <> " -p types --no-fuse")
  removeFile fp1
  h1 ← SIO.openFile fp1 WriteMode
  hPutStr h1 $ ("gg = MyLabel" ∷ Text)
  SIO.hClose h1
  tmpFile ← (</> "tmp") <$> getCanonicalTemporaryDirectory
  Main.sh (fp1 <> " -p types --no-color  --no-fuse -o" <> tmpFile)
  readFile tmpFile

ph = S.sydTest (S.it "phantom label" testPhantomLabel)

--goldenList = S.goldenTextFile "golden/goldenList" $
--  withSystemTempFile "goldenList" $ \tmpFile tmpHandle → do
--    Main.sh ("imports/list.ii -p types --no-fuse -o" <> tmpFile)
--    readFile tmpFile

goldDir = "goldenOutput/"
goldenInfer opts fName goldName = S.goldenTextFile (goldDir <> goldName) $ do
  tmpFile ← (</> "tmp" <> takeFileName fName) <$> getCanonicalTemporaryDirectory
  Main.sh (fName <> " -o" <> tmpFile <> " " <> opts)
  readFile tmpFile

list1    = S.it "list.ii"        (goldenInfer "-p types --no-fuse --no-color" "imports/list.ii"        "list")
list2    = S.it "list2.ii"       (goldenInfer "-p types --no-fuse --no-color" "imports/list2.ii"       "list2")
mutual   = S.it "mutual.ii"      (goldenInfer "-p types --no-fuse --no-color" "imports/sumMul.ii"      "sumMul")
tree     = S.it "tree.ii"        (goldenInfer "-p types --no-fuse --no-color" "imports/tree.ii"        "tree")
intmap   = S.it "intmap.ii"      (goldenInfer "-p types --no-fuse --no-color" "imports/intmap.ii"      "intmap")
mixfixes = S.it "mixfixTests.ii" (goldenInfer "-p core  --no-fuse --no-color" "imports/mixfixTests.ii" "mixfixTests")

specialise = S.it "simpleMutual.ii" (goldenInfer "-p simple  --no-color" "imports/SpecialisationTests/SimpleMutual.ii" "simpleMutual")

specTests = S.sydTest $ do
  specialise

s = S.sydTest $ do
  sequence_ fTests
  --sequence_ recTests
  caseTests
  list1
  list2
  mutual
  tree
  mixfixes
  intmap

testMixfixes = S.sydTest mixfixes
