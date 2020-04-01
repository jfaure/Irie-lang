-- Core Language
-- recall: Text >> Parse >> Core >> STG (>> LLVM >> ..)
-- The language for type judgements: checking and inferring

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

type HName     = T.Text -- human readable name
type IName     = Int    -- Int name: index into bind|type vectors
type BiSubName = Int    -- index into bisubs
type IField    = Int    -- product-type fields index
type ILabel    = Int    -- sum-type labels     index

data VName
 = VBind IName -- bind   map
 | VArg  IName -- bisub  map
 | VExt  IName -- extern map (incl. prim instrs)

data Term
 = Var     VName
 | Lit     Literal
 | App     Term    [Term] -- IName [Term]
 | MultiIf [(Term , Term)]
 | Instr   PrimInstr

 -- data constructions
 | Cons    (M.Map IField Term)
 | Proj    Term IField
 | Label   ILabel [Term] -- labels are heterogeneous lists
 | Match   (M.Map ILabel Term) (Maybe Term)
 | List    [Term]

-- Types are sampled from a
-- coproduct of profinite distributive lattices
-- typing schemes contain the monotypes of lambda-bound terms
-- a 'monotype' can be a typevar pointing to a polytype
-- type polarity corresponds to input(-) vs output(+)
type Type     = TyPlus
type Uni      = Int
type Set      = Type -- Set Uni Type
type TyCo     = [TyHead] -- same    polarity
type TyContra = [TyHead] -- reverse polarity
type TyMinus  = [TyHead] -- input  types (lattice meet) eg. args
type TyPlus   = [TyHead] -- output types (lattice join)

-- bisubs always reference themselves, so the mu. is implicit
data BiSub = BiSub { _pSub :: [TyHead] , _mSub :: [TyHead] }
newBiSub = BiSub [] []

-- components of the profinite distributive lattice of types
data TyHead -- head constructors for types.
 = THVar      BiSubName  -- index into bisubs
 | THAlias    IName      -- index into bindings
 | THArg      IName      -- lambda bound (index into monotype env)
 | THImplicit IName      -- implicit lambda bound
 | THExt      IName      -- index into externs

 | THPrim     PrimType
 | THArrow    [TyContra] TyCo
 | THRec      IName -- must be guarded (by other TyHead)
 | THProd     ProdTy
 | THSum      SumTy --incl tuples (~= var arity sum alt)
 | THArray    TyCo

 | THIxType   Type Type
 | THIxTerm   Type (Term , Type)

 | THIx       Expr
 | THEta      Term Type -- term is universe polymorphic (?!)

 | THSet      Uni
 -- Dynamic residue of types after erasure ?
type ProdTy = M.Map IField TyCo
type SumTy  = M.Map ILabel [TyCo]

-- label for the different head constructors
data Kind = KPrim | KArrow | KVar | KSum | KProd | KAny | KRec
  deriving Eq

data Expr
 = Core Term Type
 | Ty   Type  -- Set0
 | Set  Uni Type

data Bind -- indexes in the bindmap
 = WIP
 | Checking Type -- guard for recursive refs
 | BindTerm [IName] Term Type
 | BindType [Expr] Set
-- | BindType [Expr] [Expr] Set -- implicit args first

makeLenses ''BiSub

getArgTy  = \case
  Core x ty -> ty
  Ty t      -> [THSet 0]     -- type of types
  Set u t   -> [THSet (u+1)]

tyExpr = \case
  Ty t -> t
  _ -> _
