module PrettySSA where

import SSA
import Data.Text.Lazy as TL
import Data.Text.Lazy.Builder as TLB
import Prettyprinter
import Prettyprinter.Render.Util.SimpleDocTree
import Prettyprinter.Internal as P
import qualified Data.Vector as V
import qualified PrettyCore

data RenderOptions = RenderOptions
  { ansiColor  ∷ Bool
  , rawQNames  ∷ Bool
  }
ansiRender = RenderOptions {
   ansiColor  = True
 , rawQNames  = True
 }
data Annotation
 = ANone

prettySSAModule flags = render flags . layoutPretty defaultLayoutOptions . pModule
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
  doAnn prev a b = b
  in TLB.toLazyText . renderTree ANone . treeForm

pModule (Module mName typedefs exts locals) =
  "SSAModule: " <> viaShow mName <> hardline
  <> hardline <> "-- TypeDefs --" <> hardline
  <> vsep (pType <$> V.toList typedefs) <> hardline
  <> hardline <> "-- Externs --" <> hardline
  <> vsep (pFn   <$> V.toList exts) <> hardline
  <> hardline <> "-- Locals --" <> hardline
  <> vsep (pFn   <$> V.toList locals)

pExpr ∷ Expr → Doc Annotation
pExpr = \case
  Switch scrut alts def → "switch" <+> enclose "(" ")" (viaShow scrut) <> nest 2 (
    hardline <> vsep ((\(i , e) → viaShow i <+> "⇒" <+> pExpr e) <$> alts) <> hardline <> pExpr def
    )
  ECallable (Prim i) → PrettyCore.prettyInstr i
  x → viaShow x

pFn (Function decl a0 body) =
  pFnDecl decl <+> pExpr body
pFnDecl (FunctionDecl name args retTy) =
  viaShow name <+> ":" <+> hsep (punctuate " →" (pType <$> args)) <+> "→" <+> (pType retTy)
  <> hardline <> viaShow name <+> "="
pType = viaShow
