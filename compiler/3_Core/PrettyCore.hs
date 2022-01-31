module PrettyCore where
import Prim
import CoreSyn
import ShowCore()
import qualified Data.Vector as V
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
--import Text.Printf

number2CapLetter i = let
  letter = (chr ((i `mod` 26) + ord 'A'))
  overflow = i `div` 26
  in if overflow > 0 then (letter `T.cons` show overflow) else T.singleton letter
number2xyz i = let
  letter = (chr ((i `mod` 3) + ord 'x'))
  overflow = i `div` 3
  in if overflow > 0 then (letter `T.cons` show overflow) else T.singleton letter

parens x = "(" <> x <> ")"
unParens x = if T.head x == '(' then T.drop 1 (T.dropEnd 1 x) else x

prettyBind showExpr bindSrc = \case
  Checking m e g ty     -> "CHECKING: " <> show m <> show e <> show g <> " : " <> show ty
  Guard m ars tvar      -> "GUARD : " <> show m <> show ars <> show tvar
  Mutual m isRec tvar tyAnn -> "MUTUAL: " <> show m <> show isRec <> show tvar <> show tyAnn
  WIP -> "WIP"
  BindOK expr -> prettyExpr' showExpr bindSrc "\n  " expr <> "\n  "
  BindOpt complex expr -> " (" <> show complex <> ")" <> prettyExpr' showExpr bindSrc "\n  " expr <> "\n  "

prettyExpr showExpr bindSrc = prettyExpr' showExpr bindSrc ""
prettyExpr' showExpr bindSrc pad = let
  pE  = prettyExpr' showExpr bindSrc pad
  pTy = prettyTy (Just bindSrc)
  pT = prettyTerm bindSrc
  in \case
  Core term ty -> let prettyTy = clGreen  $ " : " <> unParens (pTy ty)
    in if showExpr then " = " <> pad <> pT term <> prettyTy else prettyTy
  Ty t         -> " =: " <> pad <> clGreen (pTy t)
  ExprApp f a -> pE f <> "[" <> (T.intercalate " " $ pE <$> a) <> "]"
  e -> pad <> show e

prettyVName bindSrc = \case
  VArg i     -> "λ" <> show i
  VBind i    -> let nm = toS $ (srcBindNames bindSrc) V.! i in if nm == "_" then "π" <> show i else "\"" <> nm <> "\""
  VQBind q   -> let nm = toS $ fst $ (allNames bindSrc V.! modName q) V.! unQName q in if nm == "_" then "π" <> show q else "\"" <> nm <> "\""
  VExt i     ->  "E" <> show i <> "\"" <> (toS $ (srcExtNames  bindSrc) V.! i) <> "\""
  VForeign i -> "foreign " <> show i

--prettyTerm :: _ -> _ -> _ -> _ -> Text
prettyTerm bindSrc = let
  pTy = prettyTy (Just bindSrc)
  pT  = prettyTerm  bindSrc
  pE  = prettyExpr  False bindSrc
  pET = prettyExpr  True bindSrc
  pE' = prettyExpr' True bindSrc
  prettyFree x = if IS.null x then "" else "Γ(" <> show x <> ")"
  prettyLabel l = clMagenta (prettyQName (Just (srcLabelNames bindSrc)) l)
  prettyField f = prettyQName (Just $ srcFieldNames bindSrc) f --(QName f)
  in \case
--Hole -> " _ "
  Question -> " ? "
  Var     v -> clCyan $ prettyVName bindSrc v
  Lit     l -> clMagenta $ show l
  Abs ars free term ty -> let
    prettyArg' (i , ty) = show i
    in {-pad <> -} parens $ (clYellow $ "λ " <> T.intercalate " " (prettyArg' <$> ars)) <> prettyFree free <> " => " {-<> pad-} <> pT term
     -- <> "   : " <> clGreen (pTy ty)
  App     f args -> "(" <> pT f <> clMagenta "\n  < " <> T.intercalate " " (pT <$> args) <> ")"
  PartialApp extraTs fn args -> "PartialApp " <> show extraTs <> " (" <> pT fn <> clMagenta "\n  < " <> T.intercalate " " (pT <$> args) <> ")"
  Instr   p -> "%" <> show p <> "%"
  Cast  i t -> "(" <> show i <> ")    <" <> show t <> ">"

  Cons    ts -> let
--  sr (field , val) = show field <> " " <> (toS $ (srcFieldNames bindSrc V.! modName (QName field)) V.! unQName (QName field)) <> "@" <> pT val
    sr (field , val) = prettyField (QName field) <> "@" <> pT val
    in "{ " <> (T.intercalate " ; " (sr <$> IM.toList ts)) <> " }"
--Proj    t f -> pT t <> "." <> show f <> (toS $ srcFieldNames bindSrc V.! f)
  Label   l t -> prettyLabel l <> "@" <> T.intercalate " " (parens . pET <$> t)
  RecLabel l i t -> prettyLabel l <> "(" <> show i <> ")@" <> T.intercalate " " (parens . pET <$> t)
  Match caseTy ts d -> let
    showLabel l t = prettyLabel (QName l) <> " => " <> pE' "   " t
    in clMagenta "\\case " <> clGreen (" : " <> pTy caseTy) <> ")\n    | "
      <> T.intercalate "\n    | " (IM.foldrWithKey (\l k -> (showLabel l k :)) [] ts) <> "\n    |_ " <> maybe "Nothing" pET d <> "\n"
  RecMatch ts d -> let
    showLabel l (i,t) = prettyLabel (QName l) <> "(" <> show i<> ") => " <> pE' "   " t
    in clMagenta "\\recCase " <> "\n      "
      <> T.intercalate "\n      " (IM.foldrWithKey (\l k -> (showLabel l k :)) [] ts) <> "\n     _ " <> maybe "Nothing" pET d <> "\n"

--List    ts -> "[" <> (T.concatMap pE ts) <> "]"

  TTLens r target ammo -> pT r <> " . " <> T.intercalate "." (prettyField <$> target) <> prettyLens bindSrc ammo


prettyLens bindSrc = \case
  LensGet -> " . get "
  LensSet  tt -> " . set ("  <> prettyExpr False bindSrc tt <> ")"
  LensOver cast tt -> " . over (" <> "<" <> show cast <> ">" <> prettyExpr False bindSrc tt <> ")"

prettyTyRaw = prettyTy Nothing

--prettyTy :: _ -> _ -> Type -> Text
prettyTy bindSrc = let
  pTH = prettyTyHead bindSrc
  in \case
  []  -> "_"
  [x] -> pTH x
  x   -> "(" <> (T.intercalate " & " $ pTH <$> x) <> ")"

prettyQName :: Maybe (V.Vector (V.Vector HName)) -> QName -> Text
prettyQName names q = let
  showRaw  q = show (modName q) <> "." <> show (unQName q)
  showText q names = toS $ (names V.! modName q) V.! unQName q
  in if modName q == 0
  then "!" <> show (unQName q)
  else maybe (showRaw q) (showText q) names

prettyTyHead bindSrc = let
 pTy = prettyTy bindSrc
 pTH = prettyTyHead bindSrc
 in \case
 THTop        -> "⊤"
 THBot        -> "⊥"
 THPrim     p -> prettyPrimType p
 THVar      i -> "τ" <> show i
 THBound    i -> number2CapLetter i
 THMuBound  t -> {-"μ" <>-} number2xyz t
 THMu v     t -> "μ" <> number2xyz v <> "." <> pTy t
 THExt      i -> "E" <> show i
-- THAlias    i -> "π" <> show i

 THTyCon t -> case t of
   THArrow    [] ret -> error $ toS $ "panic: fntype with no args: [] → (" <> pTy ret <> ")"
   THArrow    args ret -> parens $ T.intercalate " → " (pTy <$> (args <> [ret]))
   THSumTy   l -> let
--   prettyLabel (l,ty) = maybe (show l) (\bindSrc -> toS $ ((srcLabelNames bindSrc V.! modName (QName l)) V.! unQName (QName l))) bindSrc <> " : " <> pTy ty
     prettyLabel (l,ty) = prettyQName (srcLabelNames <$> bindSrc) (QName l) <> " : " <> pTy ty
     in "[" <> T.intercalate " | " (prettyLabel <$> IM.toList l) <> "]"
   THProduct l -> let
--   prettyField (f,ty) = maybe (show f) (\bindSrc -> toS $ ((srcFieldNames bindSrc V.! modName (QName f)) V.! unQName (QName f))) bindSrc <> " : " <> pTy ty
     prettyField (f,ty) = prettyQName (srcFieldNames <$> bindSrc) (QName f) <> " : " <> pTy ty
     in "{" <> T.intercalate " , " (prettyField <$> IM.toList l) <> "}"
   THTuple  l  -> "{" <> T.intercalate " , " (pTy <$> V.toList l) <> "}"

   THArray    t -> "Array " <> show t

-- THBi i t -> "∏(#" <> show i  <> ")" <> pTy t
 THBi i t -> "∏ " <> (T.intercalate " " $ number2CapLetter <$> [0..i-1]) <> " → " <> unParens (pTy t)
 THPi pi  -> "∏(" <> show pi <> ")"
 THSi pi arsMap -> "Σ(" <> show pi <> ") where (" <> show arsMap <> ")"
-- THCore t ty -> "↑(" <> show t <> " : " <> show ty <> ")" -- term in type context

 THSet   uni -> "Set" <> show uni
 THRecSi f ars -> "(μf" <> show f <> " $! " <> T.intercalate " " (show <$> ars) <> ")"
 THFam f ixable ix -> let
   fnTy = case ixable of { [] -> f ; x -> [THTyCon $ THArrow x f] }
   indexes = case ix of { [] -> "" ; ix -> " $! (" <> T.intercalate " " (show <$> ix) <> "))" }
   in "(Family " <> pTy fnTy <> ")" <> indexes
-- THInstr i ars -> show i <> show ars
 x -> show x

clBlack   x = "\x1b[30m" <> x <> "\x1b[0m"
clRed     x = "\x1b[31m" <> x <> "\x1b[0m" 
clGreen   x = "\x1b[32m" <> x <> "\x1b[0m"
clYellow  x = "\x1b[33m" <> x <> "\x1b[0m"
clBlue    x = "\x1b[34m" <> x <> "\x1b[0m"
clMagenta x = "\x1b[35m" <> x <> "\x1b[0m"
clCyan    x = "\x1b[36m" <> x <> "\x1b[0m"
clWhite   x = "\x1b[37m" <> x <> "\x1b[0m"
clNormal = "\x1b[0m"
