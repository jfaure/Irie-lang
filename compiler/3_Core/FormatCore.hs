module FormatCore where
{-
import Prim
import CoreSyn
import ShowCore()
import qualified PrettyCore as PC
import Prettyprinter as P

test = let
    prettyType = P.align . sep . zipWith (<+>) ("::" : repeat "->")
    prettySig name ty = pretty name <+> prettyType ty
  in prettySig ("example" :: Text) ["Int", "Bool", "Char", "IO ()"]

prettyTerm opts = \case
-}
