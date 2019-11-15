-- Type judgements: checking and inferring
-- http://pauillac.inria.fr/~remy/mlf/icfp.pdf
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/boxy-icfp.pdf

-- The goal is to check and/or infer the types of all top level bindings
-- (and the types (kinds) of the types.. etc)
--   * evaluate (static) dependent types
--   * type-check
--   * inference: reduce every type to an llvm.AST.Type

-- Inference can guess monotypes, but not polytypes

-- skolemization = remove existential quantifiers
module TypeJudge where
import Prim
import CoreSyn as C
import PrettyCore
import qualified CoreUtils as CU

import qualified Data.Vector.Mutable as MV -- mutable vectors
import Control.Monad.ST

import qualified Data.Text as T -- for cancer purposes
import qualified Data.Vector as V
import qualified Data.Map as M
import Data.Functor
import Control.Monad
import Control.Applicative
import Control.Monad.Trans.State.Strict

import qualified LLVM.AST.Constant as LC
import qualified LLVM.AST as L
import Debug.Trace

dump :: TCEnv ()
dump = traceM =<< gets (ppCoreModule . coreModule)

-- TODO use modifiable vector here!
data TCEnvState = TCEnvState { -- type check environment
   coreModule :: CoreModule
 , errors :: [TCError]
}

type TCEnv a = State TCEnvState a

judgeModule :: CoreModule -> CoreModule
judgeModule cm = handleErrors $ execState go $ TCEnvState cm []
  where go = V.imapM (judgeBind cm) (bindings cm)
        handleErrors :: TCEnvState -> CoreModule
          = \st -> case errors st of
          [] -> coreModule st
          errs -> error $ show errs

-- functions used by judgeBind and judgeExpr
lookupBindM :: IName -> TCEnv Binding
  = \n -> CU.lookupBinding n <$> gets (bindings . coreModule)
typeOfM :: IName -> TCEnv Type
  = \n -> CU.typeOfBind n    <$> gets (bindings . coreModule)
lookupHNameM :: IName -> TCEnv (Maybe HName)
  = \n -> named . info . CU.lookupBinding n 
          <$> gets (bindings . coreModule)
-- modify a binding's type annotation
updateBindTy :: IName -> Type -> TCEnv ()
  = \n ty -> 
   let doUpdate cm =
        let binds = bindings cm
            b = CU.lookupBinding n binds
            b' = b { info = (info b) { typed=ty } }
            binds' = V.modify (\v->MV.write v n b') binds
        in cm { bindings=binds' }
   in modify (\x->x{ coreModule = doUpdate (coreModule x) })

-- Rule lambda: propagate (maybe partial) type annotations downwards
-- let-I, let-S, lambda ABS1, ABS2 (pure inference case)
judgeBind :: CoreModule -> IName -> Binding -> TCEnv ()
 = \cm bindINm -> \case
  LArg    i -> pure () -- pure $ typed i
  LCon    i -> pure () -- pure $ typed i
  LClass  i -> pure () -- pure $ traceShowId $ typed i
  LExtern i -> pure () -- pure $ typed i
  LBind args e info -> let t = typed info in case t of
    expTy@(TyArrow tys) -> if length args + 1 /= length tys
      then error ("arity mismatch: " ++ 
                    show (named info) ++ show args ++ ": " ++ show tys)
      else do
        zipWithM updateBindTy args tys
        retTy  <- judgeExpr e (last tys) cm
        argTys <- mapM typeOfM args
        let fnTy = TyArrow (argTys ++ [retTy])
        updateBindTy bindINm fnTy

    t -> do
        ty <- judgeExpr e t cm
        updateBindTy bindINm ty

-- type judgements
-- a UserType of TyUnknown needs to be inferred. otherwise check it.
judgeExpr :: CoreExpr -> UserType -> CoreModule -> TCEnv Type
 = \got expected cm ->
  let
      -- local shortcuts ommitting boilerplate arguments
      unVar :: Type -> Type = CU.unVar (algData cm)
      subsume' a b = subsume a b unVar
      judgeExpr' got expected = judgeExpr got expected cm

      -- case expressions have the type of their most general alt
      mostGeneralType :: [Type] -> Maybe Type =
       let mostGeneral :: Type -> Type -> Maybe Type = \t1 t2 ->
            if | subsume' t1 t2 -> Just t1
               | subsume' t2 t1 -> Just t2
               | True           -> Nothing
       in foldr (\t1 t2 -> mostGeneral t1 =<< t2) (Just TyUnknown)

      -- inference should never return TyUnknown
      -- ('got TyUnknown' fails to subsume)
      checkOrInfer :: Type -> Type
      checkOrInfer got = case expected of
          TyUnknown -> case got of
              TyUnknown -> error "failed to subsume"
              got' -> got'
          _ -> case subsume' got expected of
              True -> got
              False -> error ("subsumption failure:"
                              ++ "\nExpected: " ++ ppType' expected
                              ++ "\nGot:      " ++ ppType' got)

  in checkOrInfer <$> case got of

  Lit l    -> pure $ expected
  WildCard -> pure expected
  Instr p  -> case expected of -- prims must be type annotated if used
      TyUnknown -> error ("primitive has unknown type: " ++ show p)
      t         -> pure expected
  Var nm ->
    -- 1. lookup type of the var in the environment
    -- 2. in checking mode, update env by filling var's boxes
    let fillBoxes :: Type -> Type -> Type
        fillBoxes boxy TyUnknown = boxy -- pure inference case
        fillBoxes boxy known = case unVar boxy of
          TyUnknown -> known
          TyArrow tys -> known -- ok ?!
          t -> known
    in do
      bindTy <- typed . info <$> lookupBindM nm
      let newTy = fillBoxes bindTy expected
      updateBindTy nm newTy
      pure newTy

  -- APP expr: unify argTypes and remove left arrows from app expresssion
  -- TODO PAP, also check arities match
  -- Typeclass resolution
  App fn args -> 
    let judgeApp tys = zipWithM judgeExpr' args (init tys)
         >>= \judged ->
         if not $ all id $ zipWith subsume' judged tys
         then error "cannot unify function arguments"
         else pure (last tys)
    in judgeExpr' fn TyUnknown <&> unVar >>= \case
      TyArrow tys -> judgeApp tys
      TyMono (MonoTyPrim prim) ->
        let toPrim = TyMono . MonoTyPrim
        in case prim of
          PrimExtern   etys -> judgeApp (toPrim <$> etys)
          PrimExternVA etys -> judgeApp (toPrim <$> etys)
      TyUnknown -> error ("failed to infer function type: "++show fn)
      t -> error ("cannot call non function: "++show fn++" : "++show t)

--Let binds inExpr -> mapM_ (judgeBind cm) binds
--                    *> judgeExpr' inExpr expected

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
    exprTys <- mapM (\(_,_,expr) -> judgeExpr' expr expected) alts
    patTys  <- mapM (\(con,args,_) -> case args of
        [] -> judgeExpr' (Var con) expected
        _  -> judgeExpr' (App (Var con) (Var <$> args)) expected
      ) alts

    let expScrutTy = case mostGeneralType patTys of
            Just t -> t
            Nothing -> error "bad case pattern"
    scrutTy <- judgeExpr' ofExpr expScrutTy

    let patsOk = all (\got -> subsume' scrutTy got)  patTys
        altsOk = all (\got -> subsume' got expected) exprTys
    pure $ if patsOk && altsOk then expected
           else error (if patsOk then "bad Alts" else "bad pats")
    -- TODO what if we don't know the expected type (in altsOK) ?
    -- use mostGeneralType probably

  unexpected -> error ("panic: tyJudge: " ++ show unexpected)

-----------------
-- Subsumption --
-----------------
-- t1 <= t2 ? is a vanilla type acceptable in the context of a (boxy) type
-- 'expected' is a vanilla type, 'got' is boxy
-- note. boxy subsumption is not reflexive
-- This requires a lookup function to deref typeAliases
subsume :: Type -> Type -> (Type -> Type) -> Bool
subsume got exp unVar = subsume' got exp
  where
  -- local subsume with freeVar TyVarLookupFn
  subsume' gotV expV =
    let got = unVar gotV
        exp = unVar expV
    in case exp of
    TyMono exp' -> case got of
      TyMono got' -> subsumeMM got' exp'
      TyPoly got' -> subsumePM got' exp'
      a -> error ("subsume: unexpected type: " ++ show a)
    TyPoly exp' -> case got of
      TyMono got'  -> subsumeMP got' exp'
      TyPoly got'  -> subsumePP got' exp'
      a -> error ("subsume: unexpected type: " ++ show a)
    TyArrow tysExp -> case got of
      TyArrow tysGot -> subsumeArrow tysGot tysExp
      TyPoly PolyAny -> True
      _ -> False
    TyExpr _ -> _
    TyUnknown -> True -- 'got' was inferred, so assume it's ok
    other -> error ("panic: unexpected type: " ++ show other)

  subsumeArrow :: [Type] -> [Type] -> Bool
  subsumeArrow got exp = all id (zipWith subsume' got exp)

  subsumeMM :: MonoType -> MonoType -> Bool
  subsumeMM (MonoTyPrim t) (MonoTyPrim t2) = t == t2
  subsumeMM (MonoRigid r) (MonoRigid r2)   = r == r2

  subsumeMP :: MonoType -> PolyType -> Bool
   = \got exp            -> case exp of
    PolyAny              -> True
    PolyConstrain tys    -> all (`subsume'` (TyMono got)) tys
    PolyUnion  tys       -> any (`subsume'` (TyMono got)) tys
    PolyData p _         -> subsumeMP got p

  subsumePM :: PolyType  -> MonoType -> Bool
--subsumePM (PolyData p _) m@(MonoRigid r) = subsumeMP m p
  subsumePM _ _ = False -- Everything else is invalid

  subsumePP :: PolyType  -> PolyType -> Bool
   = \got exp            -> case got of
    PolyAny              -> True
    PolyConstrain gTys   -> _ -- all $ f <$> tys
    -- data: use the polytypes for subsumption
    PolyData p1 _        -> case exp of
      PolyData p2 _ -> subsumePP p1 p2
      _             -> False
    PolyUnion  gTys      -> case exp of
      PolyAny            -> False
      PolyConstrain eTys -> _
      PolyUnion  eTys    -> hasAnyBy subsume' eTys gTys -- TODO check order
    where

    hasAnyBy :: (a->a->Bool) -> [a] -> [a] -> Bool
    hasAnyBy _ [] _ = False
    hasAnyBy _ _ [] = False
    hasAnyBy f search (x:xs) = any (f x) search || hasAnyBy f search xs

    localState :: State s a -> State s a
    localState f = get >>= \s -> f <* put s
