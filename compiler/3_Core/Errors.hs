module Errors where
import CoreSyn
import Data.Text as T
import Data.Vector as V
import Data.Vector.Unboxed as VU
import PrettyCore

data BiFail
  = TextMsg     Text
  | AbsentLabel QName
  | AbsentField QName
  | TyConMismatch

data TmpBiSubError = TmpBiSubError { msg :: BiFail , got :: Type , expected :: Type }
data BiSubError = BiSubError SrcOff TmpBiSubError
data CheckError = CheckError { inferredType :: Type , annotationType :: Type }
data ScopeError
  = ScopeError Text
  | AmbigBind  Text
data TCErrors = TCErrors [ScopeError] [BiSubError] [CheckError]

deriving instance Show BiFail
deriving instance Show BiSubError
deriving instance Show TmpBiSubError

formatError srcNames srcInfo (BiSubError o (TmpBiSubError failType got exp)) = let
  bindSrc = Just srcNames
  msg = let
    getName names q = if unQName q < 0
      then "!" <> show (0 - unQName q)
      else show (modName q) <> "." <> (names V.! modName q V.! unQName q)
    in case failType of
    TextMsg m     -> m
    TyConMismatch -> "Type constructor mismatch"
    AbsentField q -> "Absent field '" <> getName (srcFieldNames srcNames) q <> "'"
    AbsentLabel q -> "Absent label '" <> getName (srcLabelNames srcNames) q <> "'"

  srcLoc = case srcInfo of
    Nothing -> ""
    Just (SrcInfo text nlOff) -> let
      lineIdx = (\x -> x - 2) $ fromMaybe (0) $ VU.findIndex (> o) nlOff
      line    = (nlOff VU.! lineIdx)
      col     = o - line - 1
      in if lineIdx < 0
         then " <no source info>"
         else "\n" <> show lineIdx <> ":" <> show col <> ": \"" <> T.takeWhile (/= '\n') (T.drop o text) <> "\""
  in
     "\n" <> clRed ("No subtype: " <> msg <> ":")
  <> srcLoc
  <> "\n      " <> clGreen (toS $ prettyTy ansiRender{ bindSource = bindSrc } got)
  <> "\n  <:? " <> clGreen (toS $ prettyTy ansiRender{ bindSource = bindSrc } exp)

formatCheckError bindSrc (CheckError inferredTy annTy) = clRed "Incorrect annotation: "
  <>  "\n  inferred: " <> clGreen (prettyTy (ansiRender { bindSource = Just bindSrc }) inferredTy)
  <>  "\n  expected: " <> clGreen (prettyTy (ansiRender { bindSource = Just bindSrc }) annTy)

formatScopeError = \case
  ScopeError h -> clRed "Not in scope: "      <> h
  AmbigBind  h -> clRed "Ambiguous binding: " <> h
