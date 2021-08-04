module PrettyCore where

import Prim
import CoreSyn
import ShowCore()

import qualified Data.Vector as V
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Text.Printf

parens x = "(" <> x <> ")"
--nropOuterParens = \case { '(' : xs -> T.init xs ; x -> x }

prettyBind showExpr bindSrc bis names = \case
  Checking m e g ty -> "CHECKING: " <> show m <> show e <> show g <> " : " <> show ty
  Guard m ars tvar -> "GUARD : " <> show m <> show ars <> show tvar
  Mutual d m isRec tvar -> "MUTUAL: " <> show d <> show m <> show isRec <> show tvar
  WIP -> "WIP"
  BindOK expr -> prettyExpr' showExpr bindSrc bis names "\n  " expr <> "\n"

prettyExpr showExpr bindSrc bis names = prettyExpr' showExpr bindSrc bis names ""
prettyExpr' showExpr bindSrc bis names pad = let
  pTy = prettyTy bis names
  pT = prettyTerm bindSrc bis names
  in \case
  Core term ty -> let prettyTy = clGreen $ " : " <> pTy ty
    in if showExpr then " = " <> pad <> pT term <> prettyTy else prettyTy
  Ty t         -> " =: " <> pad <> clGreen (pTy t)
  e -> pad <> show e

prettyVName bindSrc = \case
  VArg i  -> "λ" <> show i
--VBind i -> "π" <> show i <> "\"" <> (T.unpack $ (srcBindNames bindSrc) V.! i) <> "\""
  VBind i -> let nm = toS $ (srcBindNames bindSrc) V.! i in if nm == "_" then "π" <> show i else "\"" <> nm <> "\""
  VExt i ->  "E" <> show i <> "\"" <> (toS $ (srcExtNames  bindSrc) V.! i) <> "\""

prettyTerm :: _ -> _ -> _ -> _ -> Text
prettyTerm bindSrc bis names = let
  pTy = prettyTy bis names
  pT  = prettyTerm  bindSrc bis names
  pE  = prettyExpr  False bindSrc bis names
  pE' = prettyExpr' False bindSrc bis names
  prettyFree x = if IS.null x then "" else "Γ(" <> show x <> ")"
  in \case
  Hole -> " _ "
  Var     v -> clCyan $ prettyVName bindSrc v
  Lit     l -> clMagenta $ show l
  Abs ars free term ty -> let
    prettyArg (i , ty) = "(λ" <> clYellow (show i) <> ")" -- " : " <> clGreen (pTy ty) <> ")"
    prettyArg' (i , ty) = show i
    in {-pad <> -} (clYellow $ "λ " <> T.intercalate " " (prettyArg' <$> ars)) <> prettyFree free <> " => " {-<> pad-} <> pT term
     -- <> "   : " <> clGreen (pTy ty)
  App     f args -> "(" <> pT f <> clMagenta " < " <> T.intercalate " " (pT <$> args) <> ")"
  Instr   p -> "(" <> show p <> ")"

  Cons    ts -> let
    sr (field , val) = show field <> " " <> (toS $ srcFieldNames bindSrc V.! field) <> "@" <> pT val
    in "{ " <> (T.intercalate " ; " (sr <$> IM.toList ts)) <> " }"
--Proj    t f -> pT t <> "." <> show f <> (toS $ srcFieldNames bindSrc V.! f)
  Label   l t -> prettyLabel l <> "@" <> T.intercalate " " (parens . pE <$> t)
  Match caseTy ts d -> let
    showLabel l t = prettyLabel l <> " => " <> pE' "" t
    in clMagenta "\\case " <> clGreen (" : " <> prettyTy bis names caseTy) <> ")\n    | "
      <> T.intercalate "\n    | " (IM.foldrWithKey (\l k -> (showLabel l k :)) [] ts) <> "\n    |_ " <> maybe "Nothing" pE d <> "\n"
--List    ts -> "[" <> (T.concatMap pE ts) <> "]"

  TTLens r target ammo -> pT r <> " . " <> T.intercalate "." (show <$> target) <> prettyLens bindSrc bis names ammo

prettyLabel = clMagenta . show

prettyLens bindSrc bis names = \case
  LensGet -> " . get "
  LensSet  tt -> " . set ("  <> prettyExpr False bindSrc bis names tt <> ")"
  LensOver tt -> " . over (" <> prettyExpr False bindSrc bis names tt <> ")"

prettyTyRaw = prettyTy V.empty V.empty

prettyTy :: _ -> _ -> Type -> Text
prettyTy bis names = let
  pTH = prettyTyHead bis names
  in \case
  []  -> "_"
  [x] -> pTH x
  x   -> "(" <> (T.intercalate " & " $ pTH <$> x) <> ")"

prettyTyHead bis names = let
 pTy = prettyTy bis names
 pTH = prettyTyHead bis names
 in \case
 THTop        -> "⊤"
 THBot        -> "⊥"
 THPrim     p -> prettyPrimType p
-- THArg      i -> "λ" <> show i
 THVar      i -> "τ" <> show i
 THBound    i -> "∀" <> show i
 THMuBound  t -> "μ" <> show t
 THMu v     t -> "μ" <> show v <> "." <> pTy t
-- THImplicit i -> "∀" <> show i
-- THAlias    i -> "π" <> show i
 THExt      i -> "E" <> show i
-- THRec      t -> "Rec" <> show t

 THArrow    [] ret -> error $ toS $ "panic: fntype with no args: [] → (" <> pTy ret <> ")"
 THArrow    args ret -> "(" <> T.intercalate " → " (pTy <$> (args <> [ret])) <> ")"
-- THProd     prodTy -> let
--   showField (f , t) = show f <> ":" <> show t
--   p = intercalate " ; " $ showField <$> M.toList prodTy
--   in "{" <> p <> "}"
-- THSum      sumTy ->  let
--   showLabel (l , t) = show l <> "#" <> show t
--   s  = intercalate "\n  | " $ showLabel <$> M.toList sumTy
--   in " 〈" <> s <> " 〉"
-- THSum l -> " 〈" <> show l <> " 〉"
-- THSplit l -> "Split〈" <> show l <> " 〉"
-- THProd  l -> " {" <> intercalate "," (show <$> l) <> "} "
 THSumTy  l -> "[" <> T.intercalate "," ((\(l,ty) -> show l <> " : " <> pTy ty) <$> IM.toList l) <> "]"
 THProduct  l -> "{" <> T.intercalate "," ((\(l,ty) -> show l <> " : " <> pTy ty) <$> IM.toList l) <> "}"
 THTuple  l -> "{" <> T.intercalate "," (pTy <$> V.toList l) <> "}"

 THArray    t -> "@" <> show t

 THBi i t -> "∏(#" <> show i  <> ")" <> pTy t
 THPi pi  -> "∏(" <> show pi <> ")"
 THSi pi arsMap -> "Σ(" <> show pi <> ") where (" <> show arsMap <> ")"
-- THCore t ty -> "↑(" <> show t <> " : " <> show ty <> ")" -- term in type context

 THSet   uni -> "Set" <> show uni
 THRecSi f ars -> "(μf" <> show f <> " $! " <> T.intercalate " " (show <$> ars) <> ")"
 THFam f ixable ix -> let
   fnTy = case ixable of { [] -> f ; x -> [THArrow x f] }
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
