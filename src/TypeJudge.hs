-- Type judgements: checking and inferring
-- see https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/boxy-icfp.pdf

-- The goal is to check and/or infer the types of all top level bindings
-- (and the types (kinds) of the types.. etc)
--   * evaluate (static) dependent types
--   * type-check
--   * inference: reduce every type to an llvm.AST.Type

-- Rules
-- Var: lets us increase the polymorphism of a term based on env info
-- App: (t a) has the type of the rightmost arrow (t and a's types must be known)
-- ABS1: a lambda abstraction has type (inputType -> returnType)
-- ABS2: make one box around the -> and try again (via ABS1)
-- Let-I : if let x=u in t, we have t has the same type as u
-- Let-S: same but with a user supplied type annotation for the binding
-- GEN : add some free type variables to a type judgment
--   (if they are neither in the environment nor inside boxes in the skolemized type)

-- 1. Inference can guess monotypes, but should not guess polytypes
-- 2. Use locally known information at a function call to instantiate a
-- polymorphic function !

-- we may need to make fresh unification variables during specialisation
-- (at call sites)

-- presumably let-bindings / type functions
-- skolemization = remove existential quantifiers
{-# OPTIONS -fdefer-typed-holes -Wno-typed-holes #-}
module TypeJudge where
import CoreSyn as C
import qualified CoreUtils as CU

import qualified Data.Vector.Mutable as MV -- mutable vectors
import Control.Monad.ST

import qualified Data.Vector as V
import qualified Data.Map as M
import Control.Monad
import Control.Applicative
import Control.Monad.Trans.State.Strict

import qualified LLVM.AST.Constant as LC
import qualified LLVM.AST as L
import Debug.Trace

-- ! the type of bindings needs to be updated as 
-- type information is discovered
-- TODO use modifiable vector here!
data TCEnvState = TCEnvState { -- type check environment
   coreModule :: CoreModule      -- need the module as well
 -- , binds :: VM.MVector a ExprMap -- immutable ref to mutable vector
 , errors :: [TCError]
}

type TCEnv a = State TCEnvState a
-- type TCEnv a = StateT TCEnvState (VM.MVector a Int) (ST a)
-- type TCEnv a = ReaderT TCEnvState (ST a)
-- ST is needed for our vector of type annotations (ExprMap)

judgeModule :: CoreModule -> CoreModule
judgeModule cm = handleErrors $ execState go $ TCEnvState cm []
  where go = V.mapM (judgeBind cm) (bindings cm)
        handleErrors :: TCEnvState -> CoreModule
          = \st -> case errors st of
          [] -> coreModule st
          errs -> error $ show errs

judgeBind :: CoreModule -> Binding -> TCEnv Type = \cm -> \case
  LBind args e info -> judgeExpr e (typed info) cm
  LArg i -> pure $ typed i
  LCon i -> pure $ typed i

-- type judgements
-- a UserType of TyUnknown needs to be inferred. otherwise check it.
judgeExpr :: CoreExpr -> UserType -> CoreModule -> TCEnv Type
 = \got expected cm ->
  let 
      lookupBind :: IName -> Binding
        = \n -> CU.lookupBinding n cm
      lookupType :: IName -> Type
        = \n -> CU.lookupType n cm

      -- local shortcuts ommitting boilerplate arguments
      judgeExpr' got expected = judgeExpr got expected cm
      subsume' got expected = subsume got expected lookupType

      -- case expressions have the type of their most general alt
      mostGeneralType :: [Type] -> Maybe Type
       = foldr (\t1 t2 -> mostGeneral t1 =<< t2) (Just TyUnknown)
       where
       mostGeneral :: Type -> Type -> Maybe Type = \t1 t2 -> 
        if | subsume' t1 t2 -> Just t2
           | subsume' t2 t1 -> Just t1
           | True          -> Nothing

      -- inference should never return TyUnknown
      -- ('got TyUnknown' fails to subsume)
      checkOrInfer :: Type -> Type
      checkOrInfer got = case expected of
          TyUnknown -> got -- ok
          _ -> case subsume' got expected of
              True -> got
              False -> error ("subsumption failure:"
                              ++ "\nExpected: " ++ ppType expected
                              ++ "\nGot:      " ++ ppType got)

  in checkOrInfer <$> case got of
-- VAR rule: lookup type in environement
  Var nm -> pure $ typed $ info $ lookupBind nm
  Lit l  -> pure $ typeOfLiteral l
  WildCard -> pure $ case expected of
      TyUnknown -> TyPoly ForallAny -- cannot infer more
      ty        -> ty -- assume expected type is ok

  -- APP expr: unify argTypes and remove left arrows from app expresssion
  -- TODO PAP
  App fn args -> do
    --fn <- deRefVar fn'
    --args <- mapM deRefVar args'
    judgeExpr' fn expected >>= \case
      TyArrow eArgs eRet -> zipWithM judgeExpr' args eArgs >>= \judged ->
        if all id $ zipWith subsume' judged eArgs
        then pure eRet
        else error "cannot unify function arguments"
      _ -> error ("cannot call non function: " ++ show fn)

  -- let-I, let-S, lambda ABS1, ABS2 (pure inference case)
  Let binds inExpr -> mapM_ (judgeBind cm) binds 
                      *> judgeExpr' inExpr expected

----------------------
-- Case expressions --
----------------------
-- 1. all patterns must subsume the scrutinee
-- 2. all exprs    must subsume the return type
  SwitchCase ofExpr alts ->
    let tys = mapM (\(pat, expr) -> judgeExpr' expr expected) alts
    in head <$> tys

-- dataCase: good news is we know the exact type of constructors
  DataCase ofExpr alts -> do
    scrutTy <- judgeExpr' ofExpr TyUnknown
    exprTys <- mapM (\(_,_,expr) -> judgeExpr' expr expected) alts
    patTys  <- mapM (\(con,args,_) ->
                      judgeExpr' (App (Var con) (Var <$> args)) expected) 
                    alts
    let patsOk = all (\g -> subsume' g scrutTy)  patTys
        altsOk = all (\g -> subsume' g expected) exprTys
    pure $ if patsOk && altsOk then expected else TyBroken
    -- TODO what if we don't know the expected type (in altsOK) ?
    -- use mostGeneralType probably

-----------------
-- Subsumption --
-----------------
-- t1 <= t2 ? is a vanilla type acceptable in the context of a (boxy) type
-- 'expected' is a vanilla type, 'got' is boxy
-- This requires a lookup function to deref typevars
subsume :: Type -> Type -> (IName -> Type) -> Bool
subsume got exp tyVarLookupFn = subsume' got exp
  where
  -- local subsume with freeVar TyVarLookupFn
  subsume' got' exp' = 
    let unVar (TyVar n) = tyVarLookupFn n
        unVar t = t
        got = unVar got'
        exp = unVar exp'
    in case exp of
    TyVar n -> error "internel error: tyvar wasn't dereferenced"
    TyMono exp' -> case got of
      TyMono got' -> subsumeMM got' exp'
      TyPoly got' -> subsumePM got' exp'
      a -> error ("subsume: unexpected type: " ++ show a)
    TyPoly exp' -> case got of
      TyMono got' -> subsumeMP got' exp'
      TyPoly got' -> subsumePP got' exp'
      a -> error ("subsume: unexpected type: " ++ show a)
    TyArrow argsA retA -> case got of
      TyArrow argsB retB -> subsume' retB retA
                            && all id (zipWith subsume' argsB argsA)
      TyPoly ForallAny -> True
      _ -> False
    TyExpr _ -> _
    TyUnknown -> True -- 'got' was inferred, so assume it's ok

  subsumeMM :: MonoType -> MonoType -> Bool
  subsumeMM (MonoTyLlvm t) (MonoTyLlvm t2) = t == t2
  subsumeMM (MonoTyData na) (MonoTyData nb) = na == nb
  subsumeMM _ _ = False
  
  subsumeMP :: MonoType -> PolyType -> Bool
   = \_ _ -> False
  
  subsumePM :: PolyType -> MonoType -> Bool
   = \got exp -> case got of
    ForallAny -> True
    ForallAnd tys -> all (\x -> subsume' x (TyMono exp)) tys
    ForallOr  tys -> any (\x -> subsume' x (TyMono exp)) tys
  
  subsumePP :: PolyType -> PolyType -> Bool
   = \got exp ->
    let f = _ -- hasAnyBy subsume . flip subsume exp
    in case got of
    ForallAny -> True
    ForallAnd tys -> _ --all $ f <$> tys
    ForallOr  tys -> _ -- any $ f <$> tys
    where
  
    hasAnyBy :: (a->a->Bool) -> [a] -> [a] -> Bool
    hasAnyBy _ [] _ = False
    hasAnyBy _ _ [] = False
    hasAnyBy f search (x:xs) = any (f x) search || hasAnyBy f search xs
    
    localState :: State s a -> State s a
    localState f = get >>= \s -> f <* put s
