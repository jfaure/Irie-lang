-- Type judgements: checking and inferring
-- see https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/boxy-icfp.pdf

-- The goal is to check and/or infer the types of all top level bindings
-- (and the types (kinds) of the types.. etc)
--   * evaluate (static) dependent types
--   * type-check
--   * inference: reduce every type to an llvm.AST.Type
--
-- runtime dependent types ?
--  | add runtime assertions
--  | check all functions are total
--  | do nothing (risk segfaults/weird behavior)

-- Type Judgements
-- * 'Boxes' contain outer structure of checked info, inner structure is inferred.
--   So a box denotes the border between check/inferred information.
--
-- Notation:
-- t is a monotype
-- s is a polytype
-- p is a polytype with no top level foralls
-- |s| is the boxed type s
-- s' is a boxy type (contains boxes) also note. boxes are never nested
--
-- Rules
-- Var: lets us increase the polymorphism of a term based on env info
-- App: (t a) has the type of the rightmost arrow (t and a's types must be known)
-- ABS1: a lambda abstraction has type (inputType -> returnType)
-- ABS2: make one box around the -> and try again (via ABS1)
-- Let-I : if let x=u in t, we have t has the same type as u
-- Let-S: same but with a user supplied type annotation for the binding
-- GEN : add some free type variables to a type judgment
--   (if they are neither in the environment nor inside boxes in the skolemized type)
--
-- Skol: similar to GEN but includes subsumption
-- Spec: ?
-- Mono: a <= a
-- SBoxy: if |s|~s' then |s|<=s'
-- SMono: s<=|s|
--

{-# LANGUAGE LambdaCase, MultiWayIf, ScopedTypeVariables #-}
{-# OPTIONS -fdefer-typed-holes #-}
{-# OPTIONS -Wno-typed-holes #-}
module TypeJudge where
import CoreSyn as C

import qualified Data.Vector as V
import qualified Data.Map as M
import Control.Monad
import Control.Applicative
import Control.Monad.Trans.State.Strict

import qualified LLVM.AST.Constant as LC
import qualified LLVM.AST as L
import Debug.Trace
d = trace

--m :: IO ()
--m = putStrLn (ppCoreExpr e1) *> print (judgeModule m)
--  where i32_0 = Lit $ LlvmLit $ L.ConstantOperand $ LC.Int 32 4
--        i1_1 =  Lit $ LlvmLit $ L.ConstantOperand $ LC.Int 1 1
--        defaultEntity = Entity Nothing TyUnknown 0
--
--        l1 = LBind [1] e1 defaultEntity
--        e1 = App (Var 1) [i1_1]
--
--        locals = V.fromList [LArg defaultEntity]
--
--        t = TyArrow [TyArrow [TyVar $ T.pack "ls"] (TyVar 1)] (TyVar 1) -- (a->b)->b
--        m = CoreModule V.empty (V.singleton l1) locals M.empty

judgeModule :: CoreModule -> CoreModule
judgeModule cm = handleErrors $ execState go $ TCEnvState cm []
  where go = V.mapM judgeBind (topExprs cm)
        handleErrors :: TCEnvState -> CoreModule
          = \st -> case errors st of
          [] -> coreModule st
          errs -> error $ show errs

judgeBind :: Binding -> TCEnv Type = \case
  LBind args e info -> judgeExpr e (typed info)
  LArg a -> pure TyUnknown

-- type judgements
-- a UserType of TyUnknown needs to be inferred. otherwise check against it.
-- * Inference at Variables
-- * Generalisation at let bindings
judgeExpr :: CoreExpr -> UserType -> TCEnv Type
 = \got expected ->
  let checkOrInfer :: Type -> TCEnv Type
      checkOrInfer got = pure $ case expected of
          TyUnknown -> got
          ty -> case subsume got expected of
              True -> got
              False -> error ("failed to subsume: " ++ show got)
      lookupVar :: Name -> TCEnv Binding
      lookupVar n = get >>= \env ->
          let top = topExprs $ coreModule env
              loc = localBindings $ coreModule env
              l = V.length top
              isOk = \case
                Just x -> x
                Nothing -> error (show n ++ "\n" ++ show top ++ "\n" ++ show loc)
          in pure $ isOk $ case compare n l of
          LT -> top V.!? n
          _  -> loc V.!? (n - l)
--    deRefVar :: CoreExpr -> TCEnv CoreExpr = \case
--        Var nm -> case lookupVar nm of
--            b@LBind{} -> expr b
--            l@LArg -> Var nm
--        e -> pure e
  in checkOrInfer =<< case got of
-- VAR rule: lookup type in environement
  Var nm -> typed . info <$> lookupVar nm
  Lit l  -> pure $ typeOfLiteral l
  WildCard -> pure $ case expected of
      TyUnknown -> TyPoly ForallAny -- cannot infer more
      ty        -> ty -- assume expected type is ok

-- APP expr: unify argTypes and remove left arrows from app expresssion
-- TODO PAP
  App fn args -> do
    --fn <- deRefVar fn'
    --args <- mapM deRefVar args'
    judgeExpr fn expected >>= \case
      TyArrow eArgs eRet -> zipWithM judgeExpr args eArgs >>= \judged ->
        if all id $ zipWith subsume judged eArgs
        then pure eRet
        else error "cannot unify function arguments"
      _ -> error ("cannot call non function: " ++ show fn)

-- let-I, let-S, lambda ABS1, ABS2 (pure inference case)
  Let binds inExpr -> mapM_ judgeBind binds *> judgeExpr inExpr expected

-- case: verify all alts subsume a type
  SwitchCase ofExpr alts ->
    let tys = mapM (\(pat, expr) -> judgeExpr expr expected) alts
    in head <$> tys

-----------------
-- Subsumption --
-----------------
-- t1 <= t2 ? is a vanilla type acceptable in the context of a (boxy) type
-- 'expected' is a vanilla type, 'got' is boxy
subsume :: Type -> Type -> Bool
subsume got exp = case exp of
  TyVar exp' -> _
  TyMono exp' -> case got of
    TyMono got' -> subsumeMM got' exp'
    TyPoly got' -> subsumePM got' exp'
    a -> error ("subsume: unexpected type: " ++ show a)
  TyPoly exp' -> case got of
    TyMono got' -> subsumeMP got' exp'
    TyPoly got' -> subsumePP got' exp'
    a -> error ("subsume: unexpected type: " ++ show a)
  TyArrow argsA retA -> case got of
    TyArrow argsB retB -> subsume retA retB
                          && all id (zipWith subsume argsA argsB)
    TyPoly ForallAny -> True
    _ -> False
  TyExpr _ -> _
  TyUnknown -> _ -- assume 'got' is the right type?

subsumeMM :: MonoType -> MonoType -> Bool
subsumeMM (MonoTyLlvm t) (MonoTyLlvm t2) = t == t2
subsumeMM (MonoTyData n _) (MonoTyData n2 _) = n == n2
subsumeMM _ _ = False

subsumeMP :: MonoType -> PolyType -> Bool
 = \_ _ -> False

subsumePM :: PolyType -> MonoType -> Bool
 = \got exp -> case got of
  ForallAny -> True
  ForallAnd tys -> all (\x -> subsume x (TyMono exp)) tys
  ForallOr  tys -> any (\x -> subsume x (TyMono exp)) tys

subsumePP :: PolyType -> PolyType -> Bool
 = \got exp ->
  let f = _ -- hasAnyBy subsume . flip subsume exp
  in case got of
  ForallAny -> True
  ForallAnd tys -> _ --all $ f <$> tys
  ForallOr  tys -> _ -- any $ f <$> tys

hasAnyBy :: (a->a->Bool) -> [a] -> [a] -> Bool
hasAnyBy _ [] _ = False
hasAnyBy _ _ [] = False
hasAnyBy f search (x:xs) = any (f x) search || hasAnyBy f search xs

localState :: State s a -> State s a
localState f = get >>= \s -> f <* put s
