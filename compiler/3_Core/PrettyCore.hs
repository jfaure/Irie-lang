module PrettyCore where
import Prim
import Builtins
import CoreSyn
import ShowCore()
import qualified Data.Vector as V
import qualified Data.Text as T
import qualified BitSetMap as BSM
import Data.Text.Lazy as TL
import Data.Text.Lazy.Builder as TLB
import Prettyprinter
import Prettyprinter.Render.Util.SimpleDocTree
import Prettyprinter.Internal as P
import Data.Functor.Foldable hiding (Cons)

tr t x = trace (prettyTyRaw t) x

-- HTML links:
-- <a href="#Marker></a>
-- <h1 id="Marker">There's a link to here!</h1>
data Annotation
 = ANone | AArg IName | ABindName IName | AQBindName QName | AQSpecName QName| AQLabelName QName | AQFieldName QName -- Names
 | AInstr | ALiteral | AType  | AAbs | AKeyWord | AExternType
-- | ASrcLoc -- for clickable html

data RenderOptions = RenderOptions
  { ansiColor  ∷ Bool
  , rawQNames  ∷ Bool
  , bindSource ∷ Maybe BindSource
  }
ansiRender = RenderOptions {
   ansiColor  = True
 , rawQNames  = False
 , bindSource = Nothing
 }

prettyTyRaw ∷ Type → T.Text = toS . prettyTy ansiRender
prettyTermRaw ∷ Term → T.Text = toS . prettyTerm ansiRender

prettyTy   flags      = render flags . layoutPretty defaultLayoutOptions . pTy True
prettyTerm flags      = render flags . layoutPretty defaultLayoutOptions . pTerm
prettyExpr flags      = render flags . layoutPretty defaultLayoutOptions . pExpr

prettyBind ∷ RenderOptions → Bool → T.Text → Bind → TL.Text
prettyBind flags showTerm nm b = render flags . layoutPretty defaultLayoutOptions $ pBind nm showTerm b <> hardline

--------------
-- Renderer --
--------------
-- Add markup annotations based on flags (html / ansi color / no color / raw QNames / output for unit-tests)
render ∷ RenderOptions → SimpleDocStream Annotation → TL.Text
render flags = let
  -- need to know the prev-ann so Ansi-color codes can emit the prev color
  renderTree prevAnn = \case
    STEmpty            → mempty
    STChar c           → TLB.singleton c
    STText _ t         → TLB.fromText t
    STLine i           → "\n" <> TLB.fromText (textSpaces i)
    STAnn ann contents → doAnn prevAnn ann (renderTree ann contents)
    STConcat contents  → foldMap (renderTree prevAnn) contents

  showRawQName q = show (modName q) <> "." <> show (unQName q)
  prettyQName ∷ Maybe (V.Vector (V.Vector HName)) → QName → T.Text
  prettyQName names q = let
    showText q names = toS $ (names V.! modName q) V.! unQName q
    in if modName q == 0 -- a "fieldName"; a tuple index since its in the Builtins module
    then "!" <> show (unQName q)
    else maybe (showRawQName q) (showText q) names

  doAnn ∷ Annotation → Annotation → Builder → Builder
  doAnn prev a b = let
    addColor cl b = if ansiColor flags then cl <> b <> getColor prev else b
    getColor = \case { ANone → ansiCLNormal ; AArg{} → ansiCLBlue ; AQBindName{} → ansiCLYellow
      ; ALiteral → ansiCLMagenta ; AInstr → ansiCLMagenta ; AAbs → ansiCLCyan ; AType → ansiCLGreen
      ; AKeyWord → ansiCLMagenta ; _ → ansiCLNormal }
    in case a of
    ANone         → addColor (getColor a) b
    AArg i        → addColor (getColor a)  ("λ" <> fromString (show i) <> b)
    AQSpecName  q → addColor (getColor a) $ "π" <> (fromText (showRawQName q)) <> ""
    AQBindName  q → addColor (getColor a) $ case allNames <$> bindSource flags of
      Nothing  → "π(" <> (fromText (showRawQName q)) <> ")"
      Just nms → fromText $ fst (nms V.! modName q V.! unQName q)
    AQLabelName q → {-addColor ansiCLYellow $-} b <> fromText (prettyQName (srcLabelNames <$> bindSource flags) q)
    AQFieldName q → {-addColor ansiCLYellow $-} b <> fromText (prettyQName (srcFieldNames <$> bindSource flags) q)
    ALiteral      → addColor (getColor a) b
    AInstr        → addColor (getColor a) b
    AAbs          → addColor (getColor a) b
    AType         → addColor (getColor a) b
--  AExternType i → allNames <$>
    AKeyWord      → addColor (getColor a) b
  in TLB.toLazyText . renderTree ANone . treeForm

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
number2xyz = TL.toLower . number2CapLetter
--number2xyz i = let
--  letter = (chr ((i `mod` 3) + ord 'x'))
--  overflow = i `div` 3
--  in if overflow > 0 then (letter `TL.cons` show overflow) else TL.singleton letter

pTy ∷ Bool → Type → Doc Annotation
--pTy (TyUnion t) = case t of
pTy pos = let
  pTy' = pTy pos
  latChar = if pos then "⊔" else "⊓"
  pPiArg (arg , ty) = viaShow arg <+> ":" <+> pTy' ty
  pTyUnion = \case
    [] → "_"
    [x] → pTyHead pos x
    ts  → parens $ hsep (punctuate (" " <> latChar) (pTyHeadParens pos <$> ts))
  in \case
  TyAlias q   → annotate (AQBindName q) ""
  TyVar  i    → "τ" <> viaShow i
  TyVars i [] → "τ" <> parens (hsep $ punctuate "," (viaShow <$> bitSet2IntList i))
  TyVars i g  → "τ" <> parens (hsep $ punctuate "," (viaShow <$> bitSet2IntList i)) <+> latChar <+> parens (pTyUnion g)
  TyGround u  → pTyUnion u
  TyIndexed t ars → pTy' t <+> (hsep $ parens . pExpr <$> ars)
  TyTerm term ty → parens $ pTerm term <+> ":" <+> pTy' ty
  TyPi (Pi args ty) → "Π" <> parens (hsep $ pPiArg <$> args) <+> pTy' ty
  TySi (Pi args ty) tyIndexes → _

pTyHeadParens pos t = case t of
  THTyCon THArrow{} → parens (pTyHead pos t)
  _ → pTyHead pos t

pTyHead ∷ Bool → TyHead → Doc Annotation
pTyHead pos = let
  pTy' = pTy pos
  parensIfArrow pos' t = case t of -- only add parens if necessary
    TyGround [THTyCon THArrow{}] → parens (pTy pos' t)
    _ → pTy pos' t
  in \case
  THTop        → "⊤"
  THBot        → "⊥"
  THPrim     p → pretty (prettyPrimType p)
  THBound    i → pretty (number2CapLetter i)
  THMuBound  t → pretty (number2xyz t)
  THExt      i → case snd (primBinds V.! i) of
    Ty t → pTy' t
    x → "<?? " <> viaShow x <> " ??>"

  THTyCon t → case t of
    THArrow [] ret → error $ toS $ "panic: fntype with no args: [] → (" <> prettyTy ansiRender ret <> ")"
    THArrow args ret → hsep $ punctuate " →" ((parensIfArrow (not pos) <$> args) <> [pTy' ret])
    THSumTy l → let
      prettyLabel (l,ty) = annotate (AQLabelName (QName l)) "" <> case ty of
        TyGround [THTyCon (THTuple v)] | V.null v → ""
        _ → space <> pTy' ty
      in enclose "[" "]" (hsep (punctuate (" |") (prettyLabel <$> BSM.toList l)))
    THSumOpen l d → let
      prettyLabel (l,ty) = annotate (AQLabelName (QName l)) "" <> case ty of
        TyGround [THTyCon (THTuple v)] | V.null v → ""
        _ → space <> pTy' ty
      in enclose "[" "]" (hsep (punctuate (" |") (prettyLabel <$> BSM.toList l)) <> viaShow d)
    THProduct l → let
      prettyField (f,ty) = annotate (AQFieldName (QName f)) "" <> " : " <> pTy' ty
      in enclose "{" "}" (hsep $ punctuate " ," (prettyField <$> BSM.toList l))
    THTuple  l  → enclose "{" "}" (hsep $ punctuate " ," (pTy' <$> V.toList l))
--  THArray    t → "Array " <> viaShow t

--THMu m t → "µ" <> pretty (number2CapLetter m) <> "." <> parensIfArrow t
  THMu m t → "µ" <> pretty (number2xyz m) <> "." <> parensIfArrow pos t
  THBi g t → let
    gs = if g == 0 then "" else "∏ " <> (hsep $ pretty . number2CapLetter <$> [0..g-1]) <> " → "
--  ms = if m <= 0  then "" else "µ" <> pretty (number2xyz m) <> "."
    in gs <> pTy' t
--THPi pi  → "∏(" <> viaShow pi <> ")"
--THSi pi arsMap → "Σ(" <> viaShow pi <> ") where (" <> viaShow arsMap <> ")"

  THSet   uni → "Set" <> pretty uni
  x → viaShow x

pBind nm showTerm bind = pretty nm <> " = " <> case bind of
  Guard m tvar      → "GUARD : "   <> viaShow m <> viaShow tvar
  Mutual m free isRec tvar tyAnn → "MUTUAL: " <> viaShow m <> viaShow isRec <> viaShow tvar <> viaShow tyAnn
  Queued → "Queued"
  BindOK n lbound isRec expr → let recKW = if isRec && case expr of {Core{}→True;_→False} then annotate AKeyWord "rec " else ""
    in (if lbound then "let " else "") <> if showTerm then {-viaShow n <+>-} recKW <> pExpr expr else pExprType expr
--LetBound isRec expr → let recKW = if isRec && case expr of {Core{}→True;_→False} then annotate AKeyWord "rec " else ""
--  in annotate AKeyWord "let " <> if showTerm then recKW <> pExpr expr else pExprType expr
  BindOpt complex specs expr → let
    showSpecs = if specs == 0 then "" else space <> parens "specs: " <> viaShow (bitSet2IntList specs)
    in parens ("nApps: " <> viaShow complex) <> showSpecs <+> pExpr expr

pExprType = let pos = True in \case
  Core term ty → annotate AType (pTy pos ty)
  Ty t         → " type " <> annotate AType (pTy pos t)
  ExprApp f a → pExpr f <> enclose "[" "]" (hsep $ pExpr <$> a)
  e → viaShow e

pExpr = let pos = True in \case
  Core term ty → pTerm term <> softline <> " : " <> annotate AType (pTy pos ty)
  Ty t         → "type" <+> annotate AType (pTy pos t)
  ExprApp f a → pExpr f <> enclose "[" "]" (hsep $ pExpr <$> a)
  e → viaShow e

pTerm = let
  pVName = \case
    VArg i     → annotate (AArg i)       ""
    VQBind q   → annotate (AQBindName q) ""
    VExt i     → "E" <> viaShow i -- <> dquotes (toS $ (srcExtNames bindSrc) V.! i)
    VForeign i → "foreign " <> viaShow i
  prettyLam ((Lam ars free ty) , term) = let
    prettyArg (i , ty) = viaShow i
    in (annotate AAbs $ "λ " <> hsep (prettyArg <$> ars)) <> prettyFreeArgs free <> " ⇒ " <> term
  prettyFreeArgs x = if x == 0 then "" else enclose " {" "}" (hsep $ viaShow <$> (bitSet2IntList x))
  prettyLabel l = annotate (AQLabelName l) ""
  prettyField f = annotate (AQFieldName f) ""
  prettyMatch caseTy ts d = let
--  showLabel l t = indent 2 (prettyLabel (QName l)) <+> indent 2 (pExpr t)
    showLabel l t = prettyLabel (QName l) <+> prettyLam t
    in brackets $ annotate AKeyWord "\\case " <> nest 2 ( -- (" : " <> annotate AType (pTy caseTy)) <> hardline
--    hardline <> (vsep (BSM.foldrWithKey (\l k → (showLabel l k :)) [] ts))
      hardline <> (vsep (Prelude.foldr (\(l,k) → (showLabel l k :)) [] (BSM.toList ts)))
      <> maybe "" (\catchAll → hardline <> ("_ ⇒ " <> prettyLam catchAll)) d
      )
  ppTermF = \case
  --Hole → " _ "
    QuestionF → " ? "
    VarF     v → pVName v
    VBruijnF b → "B" <> viaShow b
    LitF     l → annotate ALiteral $ parens (viaShow l)
    AbsF l     → prettyLam l
    BruijnAbsF n free body → parens $ "λB(" <> viaShow n <> prettyFreeArgs free <> ")" <+> body
    RecAppF f args → parens (annotate AKeyWord "recApp" <+> f <+> sep args)
    MatchF arg caseTy ts d → arg <+> " > " <+> prettyMatch caseTy ts d
    AppF f args    → parens (f <+> nest 2 (sep args))
    PartialAppF extraTs fn args → "PartialApp " <> viaShow extraTs <> parens (fn <> fillSep args)
    InstrF   p → annotate AInstr (prettyInstr p)
    CastF  i t → parens (viaShow i) <> enclose "<" ">" (viaShow t)
    ProdF    ts → let
      doField (field , val) = prettyField (QName field) <> ".=" <> val
      in enclose "{ " " }" (hsep $ punctuate ";" (doField <$> BSM.toList ts))
    LabelF   l []   → "@" <> prettyLabel l
    LabelF   l t    → parens $ "@" <> prettyLabel l <+> hsep (parens <$> t)
    CaseF caseID scrut → parens $ "Case" <> viaShow caseID <+> scrut
  --List    ts → "[" <> (T.concatMap pE ts) <> "]"
    TTLensF r target ammo → let
      pLens = \case
        LensGet          → " . get "
        LensSet  tt      → " . set "  <> parens (pExpr tt)
        LensOver cast tt → " . over " <> parens ("<" <> viaShow cast <> ">" <> pExpr tt)
      in r <> " . " <> hsep (punctuate "." $ prettyField <$> target) <> pLens ammo
    SpecF q    → "(Spec:" <+> annotate (AQSpecName q) "" <> ")"
  parensApp f args = parens $ parens f <+> nest 2 (sep args)
  in para $ \case
    -- parens if necessary
    AppF f args | Abs{} ← fst f → parensApp (snd f) (snd <$> args)
    x → ppTermF (fmap snd x)

prettyInstr = \case
  NumInstr i → case i of
    PredInstr GECmp → "_>_"
    IntInstr Add → "_+_"
    IntInstr Mul → "_*_"
    x → viaShow x
  p → viaShow p

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
