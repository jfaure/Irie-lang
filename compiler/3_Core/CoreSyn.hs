-- Core Language
-- recall: Text >> Parse >> Core >> STG >> LLVM
-- The target language of the inferer.

---------------------
-- Recursive Types --
---------------------
-- Recursive types are usually guarded and covariant
-- (ie. `Ma. (a->bool)->a` ok, but not `Ma. a->Bool`)
-- however,
-- FA t+ , EX t+a and tg+ where ta+ is Bottom or a,
-- ta+ is guarded in tg+ and t+ = ta+ U tg+
-- ie. guarded can be weakened to a least pre-fixed point operator mu+:
-- `mu+ a. t+ = mu a. tg+`
-- guardedness is only required to coincide mu+ and mu-
-- covariance excludes `mu a. a->a` ?
-- : look at 2 types: t1=t2->t1 and t2=t1->t2
-- can introduce mus by covariances , and
-- by substitution: `t1=mu a. (mu b. t1->b) -> a`
-- mu is monotone, so t1 and t2 are still covariant;
-- t1 = mu a'. mu a. (mu b. a' -> b) -> a
-- t1 = mu a. (mu b. a->b) -> a
-- guardedness is crucial here, to introduce mu in t2->t1
-- otherwise mu+ and mu- wouldn't be the same

--- non-regular recursion ?
-- eg. isorecursive non-regular: add opaque roll/unroll primitives

{-# LANGUAGE TemplateHaskell #-}
module CoreSyn
where

import Prim

import qualified Data.Vector         as V
import qualified Data.Text           as T
import qualified Data.Map.Strict as M
import Control.Lens hiding (List)
import Data.List (intercalate)

import Debug.Trace
d_ x   = let
  clYellow  x = "\x1b[33m" ++ x ++ "\x1b[0m"
  in trace (clYellow (show x))
did_ x = d_ x x
dv_ f = traceShowM =<< (V.freeze f)

type HName     = T.Text -- human readable name
type IName     = Int    -- Int name: index into bind|type vectors
type BiSubName = Int    -- index into bisubs
type IField    = Int    -- product-type fields index
type ILabel    = Int    -- sum-type labels     index
type CoreBinds = V.Vector Bind

data VName
 = VBind IName -- bind   map
 | VArg  IName -- bisub  map
 | VExt  IName -- extern map (incl. prim instrs)

data Term
 = Var     VName
 | Lit     Literal
 | App     Term    [Term] -- IName [Term]
 | MultiIf [(Term , Term)] Term
 | Instr   PrimInstr

 -- data constructions
 | Cons    (M.Map IField Term)
 | Proj    Term IField
 | Label   ILabel [Term]
 | Match   (M.Map ILabel Term) (Maybe Term)
 | List    [Term]

type Type     = TyPlus
type Uni      = Int
--type Set      = Type -- Set Uni Type
type TyCo     = [TyHead] -- same    polarity
type TyContra = [TyHead] -- reverse polarity
type TyMinus  = [TyHead] -- input  types (lattice meet) eg. args
type TyPlus   = [TyHead] -- output types (lattice join)
tyTOP    = []
tyBOTTOM = []

-- bisubs always reference themselves, so the mu. is implicit
data BiSub = BiSub { _pSub :: [TyHead] , _mSub :: [TyHead] }
newBiSub = BiSub [] []

-- components of our profinite distributive lattice of types
data TyHead -- head constructors for types.
 = THVar      BiSubName  -- ix to bisubs
 | THAlias    IName      -- ix to bindings
 | THArg      IName      -- lambda bound (ix to monotype env)
 | THImplicit IName      -- implicit lambda bound
 | THExt      IName      -- ix to externs

 | THPrim     PrimType
 | THArrow    [TyContra] TyCo
 | THRec      IName -- must be guarded (by other TyHead)
 | THProd     (M.Map IField TyCo) -- incl sigma
 | THSum      (M.Map ILabel [TyCo])
 | THArray    TyCo
 | THSet      Uni

 -- THTerm is only valid as part of THIxPAp (aggregate types: record, fn-arrow etc..)
 -- The goal is to cleanly separate terms from types - notably to isolate dynamic type residue
 | THTerm     IName
-- type-level (partial) application (incl dependent type)
 | THIxPAp    [IName] Type (M.Map IName Type) (M.Map IName Term)

-- label for the different head constructors
data Kind = KPrim | KArrow | KVar | KSum | KProd | KAny | KRec
  deriving Eq

data Expr
 = Core  Term Type
 | Ty    Type  -- Set0
 | Set   Uni Type

data Bind -- indexes in the bindmap
 = WIP
 | Checking  Type -- guard for recursive references

 | BindTerm  [IName] Term Type
 | BindType  [IName] Type

bind2Expr = \case
  BindTerm _ t ty -> Core t ty
  BindType _ ty -> Ty ty

makeLenses ''BiSub

getArgTy  = \case
  Core x ty -> ty
  Ty t      -> [THSet 0]     -- type of types
  Set u t   -> [THSet (u+1)]

tyExpr = \case
  Ty t -> t
  _ -> _

-- evaluate type application (from THIxPAp s)
tyAp :: [TyHead] -> M.Map IName Type -> [TyHead]
tyAp ty argMap = map go ty where
  go :: TyHead -> TyHead = \case
    THArg y -> case M.lookup y argMap of
      Nothing -> THArg y
      Just [t] -> t
    THArrow as ret -> THArrow (map go <$> as) (go <$> ret)
    x -> x
