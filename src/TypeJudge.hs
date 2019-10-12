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

-- we may need to make fresh unification variables
--
-- presumably let-bindings / type functions
-- skolemization = remove existential quantifiers
{-# OPTIONS -fdefer-typed-holes -Wno-typed-holes #-}
module TypeJudge where
import CoreSyn as C
import qualified CoreUtils as CU

import qualified Data.Vector.Mutable as MV -- mutable vectors
import Control.Monad.ST

import qualified Data.Text as T -- for cancer purposes
import qualified Data.Vector as V
import qualified Data.Map as M
import Control.Monad
import Control.Applicative
import Control.Monad.Trans.State.Strict

import qualified LLVM.AST.Constant as LC
import qualified LLVM.AST as L
import Debug.Trace

--dump :: TCEnv a
dump = gets (traceId . ppCoreModule . coreModule)

-- ! the type of bindings needs to be updated as
-- type information is discovered
-- TODO use modifiable vector here!
data TCEnvState = TCEnvState { -- type check environment
   coreModule :: CoreModule
 , errors :: [TCError]
}

type TCEnv a = State TCEnvState a

judgeModule :: CoreModule -> CoreModule
judgeModule cm = handleErrors $ execState go $ TCEnvState cm []
  where go = V.mapM (judgeBind cm) (bindings cm)
        handleErrors :: TCEnvState -> CoreModule
          = \st -> case errors st of
          [] -> coreModule st
          errs -> error $ show errs

-- functions used by judgeBind and judgeExpr
lookupBindM :: IName -> TCEnv Binding
  = \n -> CU.lookupBinding n <$> gets (bindings . coreModule)
lookupTypeM :: IName -> TCEnv Type
  = \n -> CU.lookupType n    <$> gets (bindings . coreModule)
lookupHNameM :: IName -> TCEnv (Maybe HName)
  = \n -> named . info . CU.lookupBinding n <$> gets (bindings .coreModule)
updateBindTy :: IName -> Type -> TCEnv ()
  = \n ty -> 
   let doUpdate cm =
        let binds = bindings cm
            ty = CU.lookupBinding n binds
            binds' = V.modify (\v->MV.write v n ty) binds
        in cm { bindings=binds' }
   in modify (\x->x{ coreModule = doUpdate (coreModule x) })

-- Rule lambda: propagate known type sig information downwards
judgeBind :: CoreModule -> Binding -> TCEnv Type = \cm -> \case
  LArg i -> pure $ typed i
  LCon i -> pure $ typed i
  LBind args e info -> let t = typed info in traceShow args $ case t of
    TyArrow tys -> case length args + 1 /= length tys of
      True -> error ("arity mismatch: " ++ show (named info) ++ show args ++ ": " ++ show tys)
      False -> zipWithM_ updateBindTy args tys *> dump *> judgeExpr e t cm
    -- this being a function, we need to update
    -- arguments with known type information
    _ -> judgeExpr e t cm

-- type judgements
-- a UserType of TyUnknown needs to be inferred. otherwise check it.
judgeExpr :: CoreExpr -> UserType -> CoreModule -> TCEnv Type
 = \got expected cm ->
 -- make a local pure tyVarLookupFn using tyvars at this point
 -- this is more convenient than a monadic version
  flip CU.lookupType <$> gets (bindings . coreModule) 
  >>= \tyVarLookupFn ->
  let
      unVar = \case { TyVar n -> tyVarLookupFn n ; t -> t }
      subsume' a b = subsume a b unVar
      -- local shortcuts ommitting boilerplate arguments
      judgeExpr' got expected = judgeExpr got expected cm
      -- get a type lookup function from the state monad
      --subsume' got expected = gets (bindings . coreModule) >>=
      --  \binds -> pure $ subsume got expected (flip CU.lookupType binds)

      -- case expressions have the type of their most general alt
      mostGeneralType :: (IName -> Type) -> [Type] -> Maybe Type
       = \f ->
       let mostGeneral :: Type -> Type -> Maybe Type = \t1 t2 ->
            if | subsume' t1 t2 -> Just t2
               | subsume' t2 t1 -> Just t1
               | True           -> Nothing
       in foldr (\t1 t2 -> mostGeneral t1 =<< t2) (Just TyUnknown)

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
  Lit l  -> pure $ typeOfLiteral l
  WildCard -> pure expected -- maybe return forall a.a ?
  Var nm ->
    -- 1. lookup type of the var in the environment
    -- 2. in checking mode, update env by filling var's boxes
    -- TODO expand
    let fillBoxes :: Type -> Type -> Type
        fillBoxes boxy TyUnknown = boxy -- pure inference case
        fillBoxes boxy known = case unVar boxy of
          TyUnknown -> known
          TyArrow tys -> known -- cancer
          todo -> error ("found boxy type: " ++ show todo)
    in do
      newTy <- fillBoxes expected . typed . info <$> lookupBindM nm
      hNm <- \case { Just h->h; _->T.pack ""} <$> lookupHNameM nm
      traceM (show hNm ++ show nm ++ ": " ++ ppType newTy)
      updateBindTy nm newTy
      pure newTy

  -- APP expr: unify argTypes and remove left arrows from app expresssion
  -- TODO PAP, also check arities match
  -- polymorphic instantiation ?
  App fn args -> do
    --fn <- deRefVar fn'
    --args <- mapM deRefVar args'
    judgeExpr' fn expected >>= \case
      TyArrow tys -> zipWithM judgeExpr' args (init tys) >>= \judged ->
        if all id $ zipWith subsume' judged tys
        then pure (last tys)
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
subsume :: Type -> Type -> (Type -> Type) -> Bool
subsume got exp unVar = subsume' got exp
  where
  -- local subsume with freeVar TyVarLookupFn
  subsume' got' exp' =
    let got = unVar got'
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
    TyArrow tysExp -> case got of
      TyArrow tysGot -> all id (zipWith subsume' tysGot tysExp)
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
