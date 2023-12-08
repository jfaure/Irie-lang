{-# LANGUAGE TemplateHaskell #-}
module Mixfix (solveMixfixes) where
import Prelude hiding (sourceLine)
import QName
import MixfixSyn
import ParseSyntax hiding (ParseState)
import CoreSyn(Mixfixy(..) , SrcOff)
import ShowCore()
import qualified Data.List as DL (last , init)
import Data.Functor.Foldable
import Control.Lens
import Errors

type Expr = TT
type ExprF = TTF
data ParseState = ParseState { _stream :: [Expr] }; makeLenses ''ParseState
type Parser = ExceptT Text (State ParseState)
newtype SubParser = SubParser { unSubParser :: Parser (ExprF (Either Expr SubParser)) }

-- backtracks the stream state if the parse fails
tryParse :: Parser a -> Parser a
tryParse p = use stream >>= \s -> catchE p (\e -> (stream .= s) *> throwE e)

solveMixfixes :: SrcOff -> [Expr] -> Expr
solveMixfixes srcOff juxt = (MixfixPoison . MixfixError srcOff) ||| identity
  $ runExceptT (hypoM' (solveFixities srcOff) unSubParser (parseExpr srcOff)) `evalState` ParseState juxt

solveFixities :: SrcOff -> ExprF Expr -> Expr
solveFixities srcOff = let
  clearVoids = filter (\case {VoidExpr{} -> False ; _ -> True})
  in \case
  PExprAppF _ precL fL argsL' -> let
    maybeFlipPrec precL fL argsL' = let argsL = clearVoids argsL' in case DL.last argsL of
      PExprApp _ precR fR argsR'
        | fR == fL && assoc precR == AssocNone -> MixfixPoison (MixfixError srcOff (show fR <> "Is not associative"))
        | (midArg : argsR) <- clearVoids argsR'
        , prec precL >= prec precR && (fR /= fL || assoc precR /= AssocRight)
        -- re-assoc: a L (b R c) -> (a L b) R c
        -- then recheck L in case more flips needed
        -> PExprApp srcOff precR fR (maybeFlipPrec precL fL (DL.init argsL ++ [midArg]) : argsR)
      _ -> PExprApp srcOff precL fL argsL -- R won => noop
    in maybeFlipPrec precL fL argsL'
  RawExprF e -> e
  AppF _ f ars -> App srcOff f (clearVoids ars)
  e -> embed e

uncons' :: [a] -> (Maybe a , [a])
uncons' = \case { [] -> (Nothing , []) ; x : xs -> (Just x , xs) }

-- Parser apomorphism
parseExpr :: SrcOff -> SubParser
parseExpr srcOff = SubParser $ let
  isMF = \case { MFExpr{} -> True ; _ -> False }
  mkApp = \case { [f] -> f ; f : args -> App srcOff f args ; [] -> MixfixPoison (MixfixError srcOff "impossible") }
  mkMFSubParsers :: ModuleIName -> [Maybe IName] -> [SubParser]
  mkMFSubParsers m = let
    parseMFWord q = SubParser $ stream %%= uncons' >>= \case
      Just (MFExpr _ (Mixfixy _ qs)) | QMFPart q `elem` qs -> pure VoidExprF
      m -> throwE ("Expected QMFPart " <> show q <> " , got: " <> show m)
    in map $ maybe (parseExpr srcOff) (parseMFWord . mkQName m)
  in stream %%= break isMF >>= \case
  []   -> stream %%= uncons' >>= \case -- TODO fix MFSyn: fixity of prefixes doesn't matter
    Nothing -> throwE "unexpected end of mixfix stream"
    Just (MFExpr _ (Mixfixy _ qs)) -> asum $ qs <&> \case
      QStartPrefix (MixfixDef mb mfws _fixityR) q
        -> let qvar = IQVar (VQBindIndex (mkQName (modName q) mb))
          in pure $ AppF srcOff (Left qvar) (Right <$> mkMFSubParsers (modName q) (drop 1 mfws))
      m -> throwE ("UnexpectedPreMF: " <> show m)
  larg -> let
    parsePostfix = stream %%= uncons' >>= \case
      Nothing  -> pure (RawExprF (Left $ mkApp larg)) -- trivial no-mixfix case
      Just (MFExpr _ (Mixfixy _ qs)) -> asum $ qs <&> \case
        QStartPostfix (MixfixDef mb mfws fixityL) qL
          -> pure $ PExprAppF srcOff fixityL (mkQName (modName qL) mb) (Left (mkApp larg) : (Right <$> mkMFSubParsers (modName qL) (drop 2 mfws)))
        QMFPart q -> throwE ("Unexpected QMFPart: " <> show q) -- backtracks from here
        _ -> pure (RawExprF (Left $ mkApp larg))
    in tryParse parsePostfix <|> pure (RawExprF (Left (mkApp larg)))
