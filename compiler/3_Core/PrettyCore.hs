module PrettyCore where
import Prim
import CoreSyn
import ShowCore()
import qualified Data.Vector as V
import qualified Data.Text as T
import Data.Text.Lazy as TL
import Data.Text.Lazy.Builder as TLB
import Data.IntMap as IM
import Prettyprinter
import Prettyprinter.Render.Util.SimpleDocTree
import Prettyprinter.Internal as P

-- HTML links:
-- <a href="#Marker></a>
-- <h1 id="Marker">There's a link to here!</h1>
data Annotation
 = AArg IName | ABindName IName | AQBindName  QName | AQLabelName QName | AQFieldName QName -- Names
 | AInstr | ALiteral | AType  | AAbs | AKeyWord
-- | ASrcLoc -- for clickable html

data RenderOptions = RenderOptions
  { ansiColor  :: Bool
  , rawQNames  :: Bool
  , bindSource :: Maybe BindSource
  }
ansiRender = RenderOptions {
   ansiColor  = True
 , rawQNames  = False
 , bindSource = Nothing
 }

prettyTyRaw :: Type -> T.Text
prettyTyRaw = toS . prettyTy ansiRender

prettyTy   flags      = render flags . layoutPretty defaultLayoutOptions . pTy
prettyTerm flags      = render flags . layoutPretty defaultLayoutOptions . pTerm
prettyExpr flags      = render flags . layoutPretty defaultLayoutOptions . pExpr

prettyBind :: RenderOptions -> Bool -> T.Text -> Bind -> TL.Text
prettyBind flags showTerm nm b = render flags . layoutPretty defaultLayoutOptions $ pBind nm showTerm b <> hardline

--------------
-- Renderer --
--------------
-- Add markup annotations based on flags (html / ansi color / no color / raw QNames / output for unit-tests)
render :: RenderOptions -> SimpleDocStream Annotation -> TL.Text
render flags = let
  renderTree = \case
    STEmpty            -> mempty
    STChar c           -> TLB.singleton c
    STText _ t         -> TLB.fromText t
    STLine i           -> "\n" <> TLB.fromText (textSpaces i)
    STAnn ann contents -> doAnn ann (renderTree contents)
    STConcat contents  -> foldMap renderTree contents

  showRawQName q = show (modName q) <> "." <> show (unQName q)
  prettyQName :: Maybe (V.Vector (V.Vector HName)) -> QName -> T.Text
  prettyQName names q = let
    showText q names = toS $ (names V.! modName q) V.! unQName q
    in if modName q == 0 -- a "fieldName"; a tuple index since its in the Builtins module
    then "!" <> show (unQName q)
    else maybe (showRawQName q) (showText q) names

  addColor = if ansiColor flags then addAnsiColor else \a b -> b
  doAnn :: Annotation -> Builder -> Builder
  doAnn a b = case a of
    AArg i        -> addColor ansiCLBlue    ("λ" <> fromString (show i) <> b)
    AQBindName  q -> addColor ansiCLYellow $ case allNames <$> bindSource flags of
      Nothing  -> "π" <> fromText (showRawQName q)
      Just nms -> fromText $ fst (nms V.! modName q V.! unQName q)
    AQLabelName q -> {-addColor ansiCLYellow $-} b <> fromText (prettyQName (srcLabelNames <$> bindSource flags) q)
    AQFieldName q -> {-addColor ansiCLYellow $-} b <> fromText (prettyQName (srcFieldNames <$> bindSource flags) q)
    ALiteral      -> addColor ansiCLMagenta b
    AInstr        -> addColor ansiCLMagenta b
    AAbs          -> addColor ansiCLCyan b
    AType         -> addColor ansiCLGreen   b
    AKeyWord      -> addColor ansiCLMagenta b
  in TLB.toLazyText . renderTree . treeForm

addAnsiColor cl x = cl <> x <> ansiCLNormal
ansiCLNormal  = "\x1b[0m"
ansiCLBlack   = "\x1b[30m"
ansiCLRed     = "\x1b[31m"
ansiCLGreen   = "\x1b[32m"
ansiCLYellow  = "\x1b[33m"
ansiCLBlue    = "\x1b[34m"
ansiCLMagenta = "\x1b[35m"
ansiCLCyan    = "\x1b[36m"
ansiCLWhite   = "\x1b[37m"

---------------
-- Formatter --
---------------
number2CapLetter i = let
  letter = (chr ((i `mod` 26) + ord 'A'))
  overflow = i `div` 26
  in if overflow > 0 then (letter `TL.cons` show overflow) else TL.singleton letter
number2xyz i = let
  letter = (chr ((i `mod` 3) + ord 'x'))
  overflow = i `div` 3
  in if overflow > 0 then (letter `TL.cons` show overflow) else TL.singleton letter

pTy :: Type -> Doc Annotation
pTy = \case
  [] -> "_"
  [x] -> pTyHead x
  ts  -> parens $ hsep (punctuate " &" (pTyHeadParens <$> ts))

pTyHeadParens t = case t of
  THTyCon THArrow{} -> parens (pTyHead t)
  _ -> pTyHead t

pTyHead :: TyHead -> Doc Annotation
pTyHead = \case
  THTop        -> "⊤"
  THBot        -> "⊥"
  THPrim     p -> pretty (prettyPrimType p)
  THVar      i -> "τ" <> viaShow i
  THVars     i -> "τ" <> parens (hsep $ punctuate "," (viaShow <$> bitSet2IntList i))
  THBound    i -> pretty (number2CapLetter i)
  THMuBound  t -> {-"μ" <>-} pretty (number2xyz t)
  THMu v     t -> "μ" <> pretty (number2xyz v) <> "." <> pTy t
  THExt      i -> "E" <> viaShow i

  THTyCon t -> case t of
    THArrow [] ret -> error $ toS $ "panic: fntype with no args: [] → (" <> prettyTy ansiRender ret <> ")"
    THArrow args ret -> let
      pTHArrowArg t = case t of -- only add parens if necessary
        [THTyCon THArrow{}] -> parens (pTy t)
        _ -> pTy t
--      [_] -> pTy t
--      _   -> parens (pTy t)
      in (hsep $ punctuate " →" ((pTHArrowArg <$> args) <> [pTy ret]))
    THSumTy l -> let
      prettyLabel (l,ty) = annotate (AQLabelName (QName l)) "" <> " : " <> pTy ty
      in enclose "[" "]" (hsep $ punctuate " |" (prettyLabel <$> IM.toList l))
    THProduct l -> let
      prettyField (f,ty) = annotate (AQFieldName (QName f)) "" <> " : " <> pTy ty
      in enclose "{" "}" (hsep $ punctuate " ," (prettyField <$> IM.toList l))
    THTuple  l  -> enclose "{" "}" (hsep $ punctuate " ," (pTy <$> V.toList l))
    THArray    t -> "Array " <> viaShow t

  THBi i t -> "∏ " <> (hsep $ pretty . number2CapLetter <$> [0..i-1]) <> " → " <> pTy t
  THPi pi  -> "∏(" <> viaShow pi <> ")"
  THSi pi arsMap -> "Σ(" <> viaShow pi <> ") where (" <> viaShow arsMap <> ")"

  THSet   uni -> "Set" <> pretty uni
  x -> viaShow x

pBind nm showTerm bind = pretty nm <> " = " <> case bind of
  Checking m e g ty     -> "CHECKING: " <> viaShow m <> viaShow e <> viaShow g <> " : " <> viaShow ty
  Guard m tvar      -> "GUARD : "   <> viaShow m <> viaShow tvar
  Mutual m free isRec tvar tyAnn -> "MUTUAL: " <> viaShow m <> viaShow isRec <> viaShow tvar <> viaShow tyAnn
  WIP -> "WIP"
  BindOK expr -> if showTerm then pExpr expr else pExprType expr
  BindOpt complex expr -> parens (viaShow complex) <> pExpr expr

pExprType = \case
  Core term ty -> annotate AType (pTy ty)
  Ty t         -> " =: " <> annotate AType (pTy t)
  ExprApp f a -> pExpr f <> enclose "[" "]" (hsep $ pExpr <$> a)
  e -> viaShow e

pExpr = \case
  Core term ty -> pTerm term <> softline <> " : " <> annotate AType (pTy ty)
  Ty t         -> " =: " <> annotate AType (pTy t)
  ExprApp f a -> pExpr f <> enclose "[" "]" (hsep $ pExpr <$> a)
  e -> viaShow e

pTerm = let
  pVName = \case
    VArg i     -> annotate (AArg i)       ""
    VBind i    -> error $ "not a QBind: " <> show i --annotate (ABindName i)  ""
    VQBind q   -> annotate (AQBindName q) ""
    VExt i     -> "E" <> viaShow i -- <> dquotes (toS $ (srcExtNames bindSrc) V.! i)
    VForeign i -> "foreign " <> viaShow i
  prettyLabel l = annotate (AQLabelName l) ""
  prettyField f = annotate (AQFieldName f) ""
  in \case
--Hole -> " _ "
  Question -> " ? "
  Var     v -> pVName v
  Lit     l -> annotate ALiteral (viaShow l)
  Abs ars free term ty -> let
    prettyArg (i , ty) = viaShow i
    prettyFree x = if x == 0 then "" else enclose " {" "}" (hsep $ viaShow <$> (bitSet2IntList x))
    in (annotate AAbs $ "λ " <> hsep (prettyArg <$> ars)) <> prettyFree free <> " => " <> pTerm term
--   <> ": " <> annotate AType (pTy ty)
  App f args -> parens (pTerm f <+> sep (pTerm <$> args))
  PartialApp extraTs fn args -> "PartialApp " <> viaShow extraTs <> parens (pTerm fn <> fillSep (pTerm <$> args))
  Instr   p -> annotate AInstr (viaShow p)
  Cast  i t -> parens (viaShow i) <> enclose "<" ">" (viaShow t)

  Cons    ts -> let
    doField (field , val) = prettyField (QName field) <> "@" <> pTerm val
    in enclose "{ " " }" (hsep $ punctuate ";" (doField <$> IM.toList ts))
  Label   l t    -> prettyLabel l <> "@" <> hsep (parens . pExpr <$> t)
--RecLabel l i t -> prettyLabel l <> parens (viaShow i) <> "@" <> hsep (parens . pExpr <$> t)
  Match caseTy ts d -> let
    showLabel l t = indent 2 $ prettyLabel (QName l) <> softline <> indent 2 (pExpr t)
    in annotate AKeyWord "\\case " <> (" : " <> annotate AType (pTy caseTy)) <> hardline
      <> vsep (punctuate "|" (IM.foldrWithKey (\l k -> (showLabel l k :)) [] ts))
--    <> maybe "%Default" pExpr d <> hardline
--RecMatch ts d -> let
--  showLabel l (i,t) = prettyLabel (QName l) <> "(" <> viaShow i<> ") => " <> pE' "   " t
--  in clMagenta "\\recCase " <> "\n      "
--    <> T.intercalate "\n      " (IM.foldrWithKey (\l k -> (showLabel l k :)) [] ts) <> "\n     _ " <> maybe "Nothing" pET d <> "\n"

--List    ts -> "[" <> (T.concatMap pE ts) <> "]"
  TTLens r target ammo -> let
    pLens = \case
      LensGet          -> " . get "
      LensSet  tt      -> " . set "  <> parens (pExpr tt)
      LensOver cast tt -> " . over " <> parens ("<" <> viaShow cast <> ">" <> pExpr tt)
    in pTerm r <> " . " <> hsep (punctuate "." $ prettyField <$> target) <> pLens ammo

-- Used to print error messages, but I don't like it
clBlack   x = "\x1b[30m" <> x <> "\x1b[0m"
clRed     x = "\x1b[31m" <> x <> "\x1b[0m" 
clGreen   x = "\x1b[32m" <> x <> "\x1b[0m"
clYellow  x = "\x1b[33m" <> x <> "\x1b[0m"
clBlue    x = "\x1b[34m" <> x <> "\x1b[0m"
clMagenta x = "\x1b[35m" <> x <> "\x1b[0m"
clCyan    x = "\x1b[36m" <> x <> "\x1b[0m"
clWhite   x = "\x1b[37m" <> x <> "\x1b[0m"
clNormal = "\x1b[0m"

