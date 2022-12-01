{-# LANGUAGE TypeFamilies , RecordWildCards , TemplateHaskell , FlexibleInstances , TypeSynonymInstances #-}
module Mixfix (solveMixfixes) where
import Prelude hiding (sourceLine)
import QName
import MixfixSyn
import ParseSyntax hiding (ParseState)
import CoreSyn(Mixfixy(..))
import ShowCore()
import qualified Data.List as DL (last , init)
import Data.Functor.Foldable
import Control.Lens
import MUnrolls (hypoM)

type Expr = TT
type ExprF = TTF
data ParseState = ParseState { _stream ∷ [Expr] }
makeLenses ''ParseState
type Parser = ExceptT Text (State ParseState) --type P = Prelude.State ParseState
newtype SubParser = SubParser { unSubParser ∷ Parser (ExprF (Either Expr SubParser)) }

tryParse ∷ Parser a -> Parser a
tryParse p = use stream >>= \s -> catchE p (\e -> (stream .= s) *> throwE e)

solveMixfixes ∷ [Expr] -> Expr
solveMixfixes juxt = MixfixPoison ||| identity
  $ runExceptT (hypoM (pure . solveFixities) unSubParser parseExpr) `evalState` ParseState juxt

solveFixities ∷ ExprF Expr -> Expr
solveFixities = let
  clearVoids = filter (\case {VoidExpr{} -> False ; _ -> True})
  in \case
  PExprAppF precL fL argsL' -> let
    maybeFlipPrec precL fL argsL' = let argsL = clearVoids argsL' in case DL.last argsL of
      PExprApp precR fR argsR'
        | fR == fL && assoc precR == AssocNone -> MixfixPoison (show fR <> "Is not associative")
        | (midArg : argsR) ← clearVoids argsR'
        , prec precL >= prec precR && (fR /= fL || assoc precR /= AssocRight)
        -- re-assoc: a L (b R c) -> (a L b) R c
        -- then recheck L in case more flips needed
        -> PExprApp precR fR (maybeFlipPrec precL fL (DL.init argsL ++ [midArg]) : argsR)
      _ -> PExprApp precL fL argsL -- R won ⇒ noop
    in maybeFlipPrec precL fL argsL'
  RawExprF e -> e
  AppF f ars -> App f (clearVoids ars)
  e -> embed e

-- Parser apomorphism
parseExpr ∷ SubParser
parseExpr = SubParser $ let
  isMF = \case { MFExpr{} -> True ; _ -> False }
  mkApp = \case { [f] -> f ; f : args -> App f args ; [] -> MixfixPoison "impossible" }
  mkMFSubParsers ∷ ModuleIName -> [Maybe IName] -> [SubParser]
  mkMFSubParsers m = let
    parseMFWord q = SubParser $ stream %%= splitAt 1 >>= \case
      [MFExpr (Mixfixy _ qs)] | QMFPart q `elem` qs -> pure VoidExprF
      m -> throwE ("Expected QMFPart " <> show q <> " , got: " <> show m)
    in map $ maybe parseExpr (parseMFWord . mkQName m)
  in stream %%= break isMF >>= \case
    []   -> stream %%= splitAt 1 >>= \case -- TODO fix MFSyn: fixity of prefixes doesn't matter
      [] -> throwE "empty Stream"
      [MFExpr (Mixfixy _ qs)] -> asum $ qs <&> \case
        QStartPrefix (MixfixDef _mb mfws _fixityR) q
          -> pure $ AppF (Left (QVar q)) (Right <$> mkMFSubParsers (modName q) (drop 1 mfws))
        m -> throwE ("UnexpectedPreMF: " <> show m)
      _ -> error "impossible: splitAt on MFExpr failed"
    larg -> let
      parsePostfix = stream %%= splitAt 1 >>= \case
        []  -> pure (RawExprF (Left $ mkApp larg)) -- trivial no-mixfix case
        [MFExpr (Mixfixy _ qs)] -> asum $ qs <&> \case
          (QStartPostfix (MixfixDef _mb mfws fixityL) qL)
            -> pure $ PExprAppF fixityL qL (Left (mkApp larg) : (Right <$> mkMFSubParsers (modName qL) (drop 2 mfws)))
          QMFPart q -> throwE ("Unexpected QMFPart: " <> show q) -- backtracks from here
          _ -> pure (RawExprF (Left $ mkApp larg))
        _ -> error "impossible: splitAt on MFExpr failed"
      in tryParse parsePostfix <|> pure (RawExprF (Left (mkApp larg)))
