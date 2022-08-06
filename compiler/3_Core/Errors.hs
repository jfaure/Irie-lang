{-# LANGUAGE TemplateHaskell #-}
module Errors where
import CoreSyn
import Data.Text as T
import qualified Data.Text.Lazy as TL
import Data.Vector as V
import Data.Vector.Unboxed as VU
import PrettyCore
import Control.Lens

data Errors = Errors
  { _biFails      ∷ [BiSubError]
  , _checkFails   ∷ [CheckError]
  , _scopeFails   ∷ [ScopeError]
  , _typeAppFails ∷ [TypeAppError]
--  , _tmpFails     ∷ [TmpBiSubError]
  }
emptyErrors = Errors [] [] [] []
data BiSubError = BiSubError SrcOff TmpBiSubError
data CheckError = CheckError { inferredType ∷ Type , annotationType ∷ Type }
data ScopeError
  = ScopeError Text
  | ScopeNotImported HName HName
  | AmbigBind  Text [(ModIName , IName)]
data TypeAppError = BadTypeApp { typeOperator ∷ Type , typeArgs ∷ [Expr] }

data BiFail
  = TextMsg     Text
  | AbsentLabel QName
  | AbsentField QName
  | TyConMismatch

data TmpBiSubError = TmpBiSubError { msg ∷ BiFail , got ∷ Type , expected ∷ Type }
--data TCErrors = TCErrors [ScopeError] [BiSubError] [CheckError]

makeLenses ''Errors
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
    TextMsg m     → m
    TyConMismatch → "Type constructor mismatch" <> case (got , exp) of
      (_ , TyGround [THTyCon THArrow{}]) → " (excess arguments)"
      _ → ""
    AbsentField q → "Absent field '" <> getName (srcFieldNames srcNames) q <> "'"
    AbsentLabel q → "Absent label '" <> getName (srcLabelNames srcNames) q <> "'"

  srcLoc = case srcInfo of
    Nothing → ""
    Just (SrcInfo text nlOff) → let
      lineIdx = (\x → x - 2) $ fromMaybe (0) $ VU.findIndex (> o) nlOff
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
  ScopeError h → clRed "Not in scope: "      <> h
  ScopeNotImported h m → clRed "Not in scope " <> show h <> clBlue "\nnote. ∃: "
    <> show m <> "." <> show h
  AmbigBind  h many → clRed "Ambiguous binding: " <> h <> show many

formatTypeAppError = \case
  BadTypeApp f args → clRed "Cannot normalise type operator application: "
    <> "\n    " <> prettyTy ansiRender f
    <> "\n  < " <> TL.intercalate "\n < " (prettyExpr ansiRender <$> args)
