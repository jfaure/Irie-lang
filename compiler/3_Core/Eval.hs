module Eval where
import Prim
import CoreSyn
import PrettyCore
import Data.Align
import Data.These
import qualified Data.IntMap as IM

simplifyBinds e jbs = (\(BindOK c) -> BindOK (simplifyExpr e jbs c)) <$> jbs
simplifyExpr exts jbs = \case
  Core e t -> Core (simplifyTT exts jbs e) t
  x -> x

-- Always inline simple functions
-- Constant fold casts and up to scrutinees as much as possible (can have huge impact)
-- Const args valuable for function
-- eta reduction on lambdas

-- Case merge
-- exitification (float exit paths out of recursive functions)
-- liberate-case (unroll recursive fns once to avoid repeated case on free vars)
-- Pow app
simplifyTT externs jbs = \case
  App (Var (VBind i)) args -> _
  x -> x

etaReduce :: [IName] -> [Term] -> Term -> Term
etaReduce argNms args body = let
  argList = alignWith (\case { These a b -> (a,b) ; x -> error $ "unaligned args: " <> show (argNms , args) }) argNms args
  argMap  = IM.fromList argList
  etaReduce' argMap tt = let etaReduce'' = etaReduce' argMap
    in case tt of
    Var (VArg i) | Just sub <- argMap IM.!? i -> sub
    Var{}      -> tt
    Instr{}    -> tt
    Lit{}      -> tt
    App f1 args1 -> case (etaReduce'' f1) of
      App (Instr (MkPAp n)) (f2 : args2) -> let diff = n - length args in case compare 0 diff of
        LT -> let (ok , rest) = splitAt diff (etaReduce'' <$> args2)
              in App (App (Instr (MkPAp diff)) ok) rest
        _  -> App f2 (etaReduce'' <$> (args1 ++ args2))
--      EQ -> App f2 (args1 ++ args2)
--      GT -> _ -- return function
      f -> App f (etaReduce'' <$> args1)
    Abs{}      -> error $ "eta reduce: " <> show tt
    Cons c     -> Cons (etaReduce'' <$> c)
    Label{}    -> error $ "eta reduce: " <> show tt
    Match{}    -> error $ "eta reduce: " <> show tt
    _          -> error $ "eta reduce: " <> show tt
  in etaReduce' argMap body
