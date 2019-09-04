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
-- Note on notation:
-- t is a monotype
-- s is a polytype (no top level foralls)
-- p is a polytype with top level foralls
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

module TypeJudge where
import CoreSyn as C

import qualified Data.Vector as V
import qualified Data.Map as M
import Control.Monad
import Control.Applicative

judgeModule :: CoreModule -> CoreModule
judgeModule cm =
  runState (unTCEnv $ go <* (TCEnvState cm []))
  where go = imapM judgeBind binds

-- type judgements
-- notice the 'Maybe UserType'
-- this supports a mixture of inference and checking
judgeExpr :: CoreExpr -> Maybe UserType -> TCEnv Type
judgeExpr expr userType =
  let maybeUnify ty = case userType of
         Nothing -> ty
         Just uTy -> case subsumes uTy ty of
           True -> ty
           False -> error "failed to unify"
  in case expr of
-- VAR rule: lookup type in environement
  Var nm -> maybeUnify $ lookupType nm
  Lit l  -> maybeUnify $ typeOfLiteral l

-- APP expr has the type of the rightmost arrow, as long as we can unify argtypes
  App fn args -> do
    fnTy <- judgeExpr e1
    actualArgTys <- judgeExpr <$> args
    case fnTy of
      TyArrow expectedArgTys retTy -> if all $ zipWith unify expectedTys actualTys
        then pure retTy
        else error "cannot unify function arguments"
      _ -> error "cannot call non function"

-- Let-I: also ABS1/ABS2: lambda abstractions
-- 1. we hope to check/infer using (only) the body of a binding
--    ABS1: lambda abstractions have type: args -> retType
-- 2. failing that, we have to look at it's use-sites.
--    ABS2: infer arg and ret types seperately
  Let bindings inExpr -> mapM_ addBinding bindings >>= judgeExpr inExpr
    where
      addBinding :: (Name, CoreExpr, userTy) -> TCEnv Type
      addBinding b@(Binding arity expr userTy) = do
        tcEnvAddLocals arity
        -- ABS1: to judge (\x->t):s1'->s2'
        -- we need x:s1 and |-poly t:s2' and s1'~|s1|
        -- ABS2: judge x and t seperately (probably dispatching to ABS1)
        judgeExpr userTy expr
        got <- tcEnvRemoveLocals arity


-- case: verify all alts subsume a type
  Case ofExpr alts ->
    let tys = mapM (\(pat, expr) -> judgeExpr expr) alts
    in head alts


-- check compatibility between vanilla type and a boxy type
-- 2 'flavors': 
--   t1<=t2 subsumption
--   t1~t2 boxy matching: necessary if we want to apply SBOXY: |s|<=s' iff |s|~s'
subsume :: Type -> Type -> TCEnv Bool
-- is expected>=got ? alternatively, is 'got' acceptable as an 'expected'
subsume expected got = case expected of
  TyRef a -> case got of { TyRef b -> a==b ; _ -> False }
  TyMono a -> case got of
    TyMono b -> a == b -- MONO
    TyPoly b -> vanillaSubsume a b
    TyBoxed b -> -- BMONO -- MEQ1
  TyPolo polyTy ->
  TyArrow argsA retA -> case expected of
    TyArrow argsB retB -> -- F1 and F2
      case boxyMatch argsA argsB && subsume retA retB of
        True -> True -- F1
        False -> if all isBoxed <$> argsB && isBoxed retB
                 then -- F2 (push boxes and try again)
                 else False
    _ -> False
  TyBoxed ty -> case got of
    TyBoxed g -> -- BBEQ
  TyExpr -> _ -- we must resolve this dependent type to check it

  where name2Type :: Name -> TCEnv Type

-- check if a monotype is acceptable in the context of a polytype
vanillaSubsume :: Type -> Type -> TCEnv Bool
vanillaSubsume expected got =
