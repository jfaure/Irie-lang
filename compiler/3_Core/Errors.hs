{-# LANGUAGE TemplateHaskell #-}
module Errors where
import CoreSyn
import Data.Text as T
import qualified Data.Text.Lazy as TL
import Data.Vector as V
import Data.Vector.Unboxed as VU
import PrettyCore
import Control.Lens
import MixfixSyn

data Errors = Errors
  { _biFails      :: [BiSubError]
  , _checkFails   :: [CheckError]
  , _scopeFails   :: [ScopeError]
  , _typeAppFails :: [TypeAppError]
  , _mixfixFails  :: [MixfixError]
  , _unpatternFails::[UnPatError]
  , _scopeWarnings::[ScopeWarning]
--, _parseFails   :: [Text]
--  , _tmpFails     :: [TmpBiSubError]
  }
emptyErrors = Errors [] [] [] [] [] [] []
data BiSubError = BiSubError SrcOff TmpBiSubError
data CheckError = CheckError { inferredType :: Type , annotationType :: Type } | ExpectedType Expr
data ScopeError
  = ScopeError Text
  | NoScopeLabel IName Int
  | ScopeNotOpened BitSet VQBindIndex -- this QName is a BindIndex, not an IName!
  | ScopeNotOpenedINames BitSet [QName]
  | AmbigBind  Text [(ModIName , IName)]
  | ScopeLetBound IName
  | LetConflict ModIName BitSet -- [Text]
  deriving Show
data ScopeWarning
  = LetShadows BitSet
  | LambdaShadows BitSet
  | RedundantPatMatch deriving Show
data TypeAppError = BadTypeApp { typeOperator :: Type , typeArgs :: [Expr] }
data MixfixError  = MixfixError SrcOff Text deriving Show
data UnPatError   = RedundantPatternMatch Text | NoCaseMerge Text | EmptyCase | IllegalPattern Text
  | UnknownLabelExtern Int | UnknownLabelApp Int deriving Show

data BiFail
  = TextMsg     Text
  | AbsentLabel QName
  | AbsentField QName
  | TyConMismatch

data TmpBiSubError = TmpBiSubError { msg :: BiFail , got :: Type , expected :: Type }
--data TCErrors = TCErrors [ScopeError] [BiSubError] [CheckError]

makeLenses ''Errors
deriving instance Show BiFail
deriving instance Show BiSubError
deriving instance Show TmpBiSubError

formatSrcLoc srcInfo o = case srcInfo of
  Nothing -> ""
  Just (SrcInfo text nlOff) -> let
    lineIdx = (+1) $ fromMaybe 0 (VU.findIndex (> o) nlOff)
    line    = nlOff VU.! lineIdx
    col     = line - o
    in if lineIdx < 0
       then "<no source info>"
       else "\n" <> show lineIdx <> ":" <> show col <> ": " <> T.takeWhile (/= '\n') (T.drop o text)

getName nameFn q = if unQName q < 0 -- (names V.! modName q V.! unQName q)
  then "!" <> show (0 - unQName q)
  else show (modName q) <> "." <> fromMaybe (showRawQName q) (nameFn (modName q) (unQName q))

formatBisubError srcNames srcInfo (BiSubError src (TmpBiSubError failType got exp)) = let
  bindSrc = Just srcNames
  msg = case failType of
    TextMsg m     -> m
    TyConMismatch -> "Type constructor mismatch" <> case (got , exp) of
      (_ , TyGround [THTyCon THArrow{}]) -> " (excess arguments)"
      _ -> ""
    AbsentField q -> "Absent field '" <> showRawQName q <> "'"
    AbsentLabel q -> "Absent label '" <> getName (srcINames srcNames) q <> "'"
  in
     clRed ("No subtype: " <> msg <> ":")
  <> formatSrcLoc srcInfo src
  <> "\n    " <> clGreen (toS $ prettyTy ansiRender{ bindSource = bindSrc } got)
  <> "\n<:? " <> clGreen (toS $ prettyTy ansiRender{ bindSource = bindSrc } exp)

formatCheckError :: BindSource -> CheckError -> Text
formatCheckError bindSrc (CheckError inferredTy annTy) = clRed "Incorrect annotation: "
  <>  "\n  inferred: " <> clGreen (TL.toStrict $ prettyTy (ansiRender { bindSource = Just bindSrc }) inferredTy)
  <>  "\n  expected: " <> clGreen (TL.toStrict $ prettyTy (ansiRender { bindSource = Just bindSrc }) annTy)
formatCheckError bindSrc (ExpectedType expr) = clRed "Annotation is not a type: " <> toS (prettyExpr ansiRender expr)

getIName bindSrc modIName i = fromMaybe (show i) ((srcINames bindSrc) modIName i)
getBindName bindSrc modIName i = fromMaybe (show i) ((srcBindNames bindSrc) modIName i)

formatScopeError thisMod bindSrc = \case
  ScopeError h -> clRed "Not in scope: "      <> h
  NoScopeLabel i n -> clRed "Not in scope: label " <> show (getIName bindSrc thisMod i) <> " (Applied to " <> show n <> " args)"
  ScopeLetBound i -> clRed "let-bound not in scope: "      <> show i
  ScopeNotOpened opens (VQBindIndex q) -> clRed "Not in scope " <> getBindName bindSrc (modName q) (unQName q)
    <> clBlue "\nnote. ∃: " <> showRawQName q
  ScopeNotOpenedINames opens qs -> let -- mixfix words were loaded but none are in scope
    qHNames = qs <&> \q -> getIName bindSrc (modName q) (unQName q)
    in clRed "Not in scope: " <> show (fromMaybe "?! empty mixfixwords list" (Prelude.head qHNames))
  AmbigBind h many -> clRed "Ambiguous binding: " <> h <> show many
  LetConflict modIName many -> let
    in case bitSet2IntList many of
    [one] -> clRed "Let conflict: " <> getIName bindSrc modIName one
    many  -> clRed "Let conflicts: " <> T.intercalate " , " (getIName bindSrc modIName <$> many)

formatTypeAppError = \case
  BadTypeApp f args -> TL.toStrict $ clRed "Cannot normalise type operator application: "
    <> "\n    " <> prettyTy ansiRender f
    <> "\n  < " <> TL.intercalate "\n < " (prettyExpr ansiRender <$> args)

formatMixfixError srcInfo = \case
  MixfixError o msg ->
     "\n" <> clRed ("Mixfix parse failure: " <> msg <> ":")
    <> formatSrcLoc srcInfo o

formatUnPatError = \case
  RedundantPatternMatch txt -> "RedundantPatternMatch: " <> show txt
  NoCaseMerge txt -> "No case merge: " <> txt
  EmptyCase -> "Empty Case"
  IllegalPattern txt -> "Illegal pattern: " <> txt
  UnknownLabelExtern i -> "Unknown label extern: " <> show i
  UnknownLabelApp    q -> "Unknown label app: " <> show q

formatScopeWarnings iNames = \case
  LetShadows bs -> "Let shadow: " <> T.intercalate " , "  ((iNames V.!) <$> bitSet2IntList bs)
  LambdaShadows bs -> "λ shadow: " <> T.intercalate " , " ((iNames V.!) <$> bitSet2IntList bs)
  RedundantPatMatch -> "Redundant pattern match"
