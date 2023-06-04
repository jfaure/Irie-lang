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
import Data.Functor.Foldable

traceTy t x = trace (prettyTyRaw t) x
traceTerm t x = trace (prettyTermRaw t) x

-- HTML links:
-- <a href="#Marker></a>
-- <h1 id="Marker">There's a link to here!</h1>
data Annotation
 = ANone | AArg IName | AQRawName QName | AQBindName QName | AQSpecName QName| AQLabelName QName | AQFieldName QName -- Names
 | ARawFieldName HName | ARawLabelName HName
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

prettyTyRaw   :: Type -> T.Text = toS . prettyTy ansiRender
prettyTermRaw :: Term -> T.Text = toS . prettyTerm ansiRender

prettyTy   flags = render flags . layoutPretty defaultLayoutOptions . pTy   True
prettyTerm flags = render flags . layoutPretty defaultLayoutOptions . pTerm True
prettyExpr flags = render flags . layoutPretty defaultLayoutOptions . pExpr True

-- ! empty letmetas
prettyBind :: RenderOptions -> Bool -> T.Text -> Bind -> TL.Text
prettyBind flags showTerm nm b = render flags . layoutPretty defaultLayoutOptions $ pBind nm showTerm b <> hardline

prettyJudgedModule :: Bool -> Bool -> RenderOptions -> JudgedModule -> TL.Text
prettyJudgedModule showLetBinds showRhs flags j = render flags . layoutPretty defaultLayoutOptions
  $ pJM showLetBinds showRhs j

-- want to print the top-level let-block without {} or = record
pJM showLetBinds showRhs jm = let
  isTopBind (lm , _) = isTop lm
  binds = toList (if showLetBinds then moduleTT jm else V.takeWhile isTopBind (moduleTT jm))
  in vsep ((\(nm , b) -> pBind (hName nm) showRhs b) <$> binds)

--------------
-- Renderer --
--------------
-- Add markup annotations based on flags (html / ansi color / no color / raw QNames / output for unit-tests)
render :: RenderOptions -> SimpleDocStream Annotation -> TL.Text
render flags = let
  -- need to know the prev-ann so Ansi-color codes can emit the prev color
  renderTree prevAnn = \case
    STEmpty            -> mempty
    STChar c           -> TLB.singleton c
    STText _ t         -> TLB.fromText t
    STLine i           -> "\n" <> TLB.fromText (textSpaces i)
    STAnn ann contents -> doAnn prevAnn ann (renderTree ann contents)
    STConcat contents  -> foldMap (renderTree prevAnn) contents

  prettyQName :: Bool -> Maybe (ModIName -> IName -> Maybe HName) -> QName -> T.Text
  prettyQName isField names q = let -- (names V.! modName q) V.! unQName q
    iName = unQName q
    showText q nameFn = if iName < 0 then "!!" <> show iName else -- (- iName - 1) else
      toS $ fromMaybe (showRawQName q) $ nameFn (modName q) (unQName q)
    isBuiltin = modName q == 0
    in (if isBuiltin then "!" else "") <> if isField && isBuiltin then show (unQName q) else
      maybe (showRawQName q) (showText q) names

  doAnn :: Annotation -> Annotation -> Builder -> Builder
  doAnn prev a b = let
    addColor cl b = if ansiColor flags then cl <> b <> getColor prev else b
    getColor = \case { ANone -> ansiCLNormal ; AArg{} -> ansiCLBlue ; AQBindName{} -> ansiCLYellow
      ; ALiteral -> ansiCLMagenta ; AInstr -> ansiCLMagenta ; AAbs -> ansiCLCyan ; AType -> ansiCLGreen
      ; AKeyWord -> ansiCLMagenta ; _ -> ansiCLNormal }
    in case a of
    ANone         -> addColor (getColor a) b
    AArg i        -> addColor (getColor a)  ("λ" <> fromString (show i) <> b)
    AQSpecName  q -> addColor (getColor a) $ "π" <> (fromText (showRawQName q)) <> ""
    AQRawName   q -> addColor (getColor a) $ fromText (showRawQName q)
    AQBindName  q -> addColor (getColor a) $ case srcFieldNames <$> bindSource flags of
      Nothing  -> "π(" <> (fromText (showRawQName q)) <> ")"
      Just fn -> fromText (fromMaybe (showRawQName q) $ fn (modName q) (unQName q))
      -- (fst (nms V.! modName q V.! unQName q))
    AQLabelName q -> {-addColor ansiCLYellow $-} b <> fromText (prettyQName False (srcLabelNames <$> bindSource flags) q)
--  AQFieldName q -> {-addColor ansiCLYellow $-} b <> fromText (prettyQName (srcFieldNames <$> bindSource flags) q)
    AQFieldName q -> -- if modName q == 0 then "!" <> fromText (show (unQName q)) else
      {-addColor ansiCLYellow $-} b <> fromText (prettyQName True (srcFieldNames <$> bindSource flags) q)
    ARawFieldName q -> fromText q
    ARawLabelName q -> fromText q
    ALiteral      -> addColor (getColor a) b
    AInstr        -> addColor (getColor a) b
    AAbs          -> addColor (getColor a) b
    AType         -> addColor (getColor a) b
    AKeyWord      -> addColor (getColor a) b
  in TLB.toLazyText . renderTree ANone . treeForm

addAnsiColor cl x = cl <> x <> ansiCLNormal
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

pTy :: Bool -> Type -> Doc Annotation
pTy pos = let
  pTy' = pTy pos
  latChar = if pos then "⊔" else "⊓"
  pPiArg (arg , ty) = viaShow arg <+> ":" <+> pTy' ty
  pTyUnion = \case
    []  -> if pos then "⊥" else "⊤"
    [x] -> pTyHead pos x
    ts  -> parens $ hsep (punctuate (" " <> latChar) (pTyHeadParens pos <$> ts))
  in \case
  TyAlias q   -> annotate (AQBindName q) ""
  TyVars i [] -> "τ" <> parens (hsep $ punctuate "," (viaShow <$> bitSet2IntList i))
  TyVars i g  -> "τ" <> parens (hsep $ punctuate "," (viaShow <$> bitSet2IntList i)) <+> latChar <+> parens (pTyUnion g)
  TyGround u  -> pTyUnion u
  TyIndexed t ars -> pTy' t <+> (hsep $ parens . pExpr False <$> ars)
  TyTerm term ty -> parens $ pTerm True term <+> ":" <+> pTy' ty
  TyPi (Pi args ty) -> "Π" <> parens (hsep $ pPiArg <$> args) <+> pTy' ty
  TySet n -> "Set" <> viaShow n
  TySi{} -> "TySi{}"

pTyHeadParens pos t = case t of
  THTyCon THArrow{} -> parens (pTyHead pos t)
  _ -> pTyHead pos t

pTyHead :: Bool -> TyHead -> Doc Annotation
pTyHead pos = let
  pTy' = pTy pos
  parensIfArrow pos' t = case t of -- only add parens if necessary
    TyGround [THTyCon THArrow{}] -> parens (pTy pos' t)
    _ -> pTy pos' t
  in \case
  THTop        -> "⊤"
  THBot        -> "⊥"
  THPrim     p -> pretty (prettyPrimType p)
  THBound    i -> pretty (number2CapLetter i)
  THMuBound  t -> pretty (number2xyz t)
  THExt      i -> case snd (primBinds V.! i) of
    (Core (Ty t) _) -> pTy' t
    x -> "<?? " <> viaShow x <> " ??>"

  THTyCon t -> case t of
    THArrow [] ret -> error $ toS $ "panic: fntype with no args: [] -> (" <> prettyTy ansiRender ret <> ")"
    THArrow args ret -> hsep $ punctuate " →" ((parensIfArrow (not pos) <$> args) <> [pTy' ret])
    THSumTy l -> let
      prettyLabel (l,ty) = annotate (AQLabelName (QName l)) "" <> case ty of
        TyGround [THTyCon (THTuple v)] | V.null v -> ""
        _ -> space <> pTy' ty
      in enclose "[" "]" (hsep (punctuate (" |") (prettyLabel <$> BSM.toList l)))
    THSumOpen l -> let
      prettyLabel (l,ty) = annotate (AQLabelName (QName l)) "" <> case ty of
        TyGround [THTyCon (THTuple v)] | V.null v -> ""
        ty -> space <> pTy' ty
      in enclose "[" "]" (hsep (punctuate (" |") (prettyLabel <$> BSM.toList l)) <+> "| _")
    THArray eTy -> parens $ "Array" <+> pTy' eTy
    THProduct l -> let
      prettyField (f,ty) = annotate (AQFieldName (QName f)) "" <> " : " <> pTy' ty
      in enclose "{" "}" (hsep $ punctuate " ," (prettyField <$> BSM.toList l))
    THTuple  l  -> enclose "{" "}" (hsep $ punctuate " ," (pTy' <$> V.toList l))
--  THArray    t -> "Array " <> viaShow t

  THMu m t -> "µ" <> pretty (number2xyz m) <> "." <> parensIfArrow pos t
  THBi g t -> let
    gs = if g == 0 then "" else "∏ " <> (hsep $ pretty . number2CapLetter <$> [0..g-1]) <> " → "
--  ms = if m <= 0  then "" else "µ" <> pretty (number2xyz m) <> "."
    in gs <> pTy' t
--THPi pi  -> "∏(" <> viaShow pi <> ")"
--THSi pi arsMap -> "Σ(" <> viaShow pi <> ") where (" <> viaShow arsMap <> ")"
--THSet   uni -> "Set" <> pretty uni
  x -> viaShow x

pBind :: HName -> Bool -> Bind -> Doc Annotation
pBind nm showRhs bind = pretty nm <> " = " <> case bind of
  Guard m tvar      -> "GUARD : " <> viaShow m <> viaShow tvar
  Mut{}             -> "Mut{} "
  BindOK _n (nFree , free) expr -> let
    recKW = "" -- if isRec && case expr of {Core{} -> True ; _ -> False} then annotate AKeyWord "rec " else ""
    letW  = "" -- if lbound then "let " else ""
    in letW <> {-viaShow n <+> -} recKW <> (if 0 == free then "" else viaShow (nFree , bitSet2IntList free)) <> pExpr showRhs expr

pExpr :: Bool -> Expr -> Doc Annotation
pExpr showRhs (Core term ty) = let pos = True in case term of
  LetBlock{} -> (if showRhs then pTerm showRhs term <+> ": " else "") <> annotate AType (pTy True ty)
--  -> nest 2 $ vsep ((\(nm , b) -> pBind (hName nm) showRhs b) <$> toList bs)
  term       -> (if showRhs then pTerm showRhs term <+> ": " else "") <> annotate AType (pTy pos ty)

pTerm :: Bool -> Term -> Doc Annotation
pTerm showRhs = let
  pVName = \case
    VQBind q   -> annotate (AQBindName q) ""
    VForeign i -> "foreign " <> viaShow i
  prettyLabel l = annotate (AQLabelName l) ""
--prettyField f = annotate (AQFieldName f) ""
  prettyMatch prettyLam _caseTy ts d = let
    showLabel l t = prettyLabel (QName l) <+> "=>" <+> prettyLam t
    in brackets $ annotate AKeyWord "\\case" <> nest 2 ( -- (" : " <> annotate AType (pTy caseTy)) <> hardline
      hardline <> (vsep (Prelude.foldr (\(l,k) -> (showLabel l k :)) [] (BSM.toList ts)))
      <> maybe "" (\catchAll -> hardline <> ("_ => " <> prettyLam catchAll)) d
      )
  ppTermF = \case
    TyF t -> pTy True t -- TODO polarity
    QuestionF -> " ? "
    VarF     v -> pVName v
    VBruijnF b -> "B" <> viaShow b
    VBruijnLevelF b -> "BL" <> viaShow b
    LitF     l -> annotate ALiteral $ parens (viaShow l)
    BruijnAbsF n body -> parens $ "λb(" <> viaShow n <> ")" <+> body
    BruijnAbsTypedF n body argMetas retTy -> parens $ "λB(" <> viaShow n <> ")" <+> body
    CaseBF  arg _ty ts d -> arg <+> " > " <+> prettyMatch identity Nothing ts d
    CaseSeqF _n arg _ty ts d -> arg <+> " caseSeq> " <+> prettyMatch identity Nothing ts d
    AppF f args    -> parens (f <+> nest 2 (sep args))
    InstrF   p -> annotate AInstr (prettyInstr p)
    X86IntrinsicF t -> annotate AInstr (viaShow t)
    CastF  i t -> parens (viaShow i) <> enclose "<" ">" (viaShow t)
    LabelF   l [] -> "@" <> prettyLabel l
    LabelF   l t  -> parens $ "@" <> prettyLabel l <+> hsep (parens <$> t)
--  CaseF caseID scrut -> parens $ "Case" <> viaShow caseID <+> scrut
  --List    ts -> "[" <> (T.concatMap pE ts) <> "]"
    TTLensF r target ammo -> let
      pLens = \case
        LensGet          -> " . get "
        LensSet  tt      -> " . set "  <> parens (pExpr showRhs tt)
        LensOver cast tt -> " . over " <> parens ("<" <> viaShow cast <> ">" <> pExpr showRhs tt)
      in parens $ r <> " . " <> hsep (punctuate "." $ {-prettyField-} viaShow <$> target) <> pLens ammo
    LetSpecF q sh -> "let-spec: " <> viaShow q <> "(" <> viaShow sh <> ")"
    PoisonF t    -> parens $ "poison " <> unsafeTextWithoutNewlines t
    ProdF ts     -> braces $ hsep $ punctuate " ," (BSM.toList ts <&> \(l , rhs) -> annotate (AQFieldName (QName l)) "" <> " = " <> rhs)

    ArrayF ts    -> parens $ "#" <+> hsep (V.toList ts)
    TupleF ts    -> parens $ hsep $ punctuate " ," (V.toList ts)
    LetBindsF bs t -> "let" <> nest 2 (hardline <> vsep ((\(nm , b) -> pBind (hName nm) showRhs b) <$> toList bs))
      <> hardline <> "in" <+> t
    LetBlockF bs   -> enclose "{" "}" $ hsep $ punctuate " ;" ((\(nm , b) -> pBind (hName nm) showRhs b) <$> toList bs)
--  LetBlockF bs   -> nest 2 $ vsep ((\(nm , b) -> pBind (hName nm) showRhs b) <$> toList bs)

  parensApp f args = parens $ parens f <+> nest 2 (sep args)
  in para $ \case
    -- parens if necessary
    AppF f args | BruijnAbs{} <- fst f -> parensApp (snd f) (snd <$> args)
    x -> ppTermF (snd <$> x)

prettyInstr = \case
  NumInstr i -> case i of
    PredInstr GECmp -> "_>=?_"
    PredInstr GTCmp -> "_>?_"
    PredInstr LTCmp -> "_<?_"
    PredInstr LECmp -> "_<=?_"
    IntInstr Add    -> "_+_"
    IntInstr Sub    -> "_-_"
    IntInstr Mul    -> "_*_"
    IntInstr SDiv   -> "_//_"
    x -> viaShow x
  p -> viaShow p

ansiCLNormal  = "\x1b[0m"
ansiCLBlack   = "\x1b[30m"
ansiCLRed     = "\x1b[31m"
ansiCLGreen   = "\x1b[32m"
ansiCLYellow  = "\x1b[33m"
ansiCLBlue    = "\x1b[34m"
ansiCLMagenta = "\x1b[35m"
ansiCLCyan    = "\x1b[36m"
ansiCLWhite   = "\x1b[37m"

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
