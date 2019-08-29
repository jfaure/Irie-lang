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

-- {-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- Type Judgements
-- * 'Boxes' contain outer structure of checked info, inner structure is inferred.
--   So a box denotes the border between check/inferred information.
--
-- Rules
-- Var: lets us increase the polymorphism of a term based on env info
-- App: (t a) has the type of the rightmost arrow (t and a's types must be known)
-- ABS1: a lambda abstraction has type (inputType -> returnType)
-- ABS2: make one box around the -> and try again (via ABS1)
-- Let-I : if let x=u in t, we have t has the same type as u
-- Let-S: same but with a user supplied type annotation for the binding
-- GEN : add some free type variables to a type judgment (if they are neither in the environment nor inside boxes in the skolemized type)
-- --
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
judgeModule (CoreModule env binds) =
  imapM judgeBind binds

-- type check environment
data TCEnv = TCEnv {
  -- subsumption information
  -- type anntoations
  bindings :: V.Vector Entity
  boxyMatches :: V.Vector Polytype -- we need to fill in boxes with monotypes
}

judgeExpr :: Environment -> CoreExpr -> Environment

monomize :: Environment -> Type -> Type
--
-- Judging
-- upwards   is inference
-- downwards is checking
--judgeTopBind :: Name -> CoreExpr -> CoreExpr
--judgeTopBind nm e =
--  let info = env ! nm in
--  case typed info of
--    TyUnknown -> infer
--    TyBoxed t -> infer
--    vanillaTy -> check vanillaTy
