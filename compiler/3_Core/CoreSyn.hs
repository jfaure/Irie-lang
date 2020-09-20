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
{-# OPTIONS  -funbox-strict-fields #-}
module CoreSyn
where

import Prim

import qualified Data.Vector         as V
import qualified Data.Text           as T
import qualified Data.IntMap.Strict  as IM
import qualified Data.IntSet         as IS
import Control.Lens hiding (List)
import Debug.Trace

d_ x   = let
  clYellow  x = "\x1b[33m" ++ x ++ "\x1b[0m"
  in trace (clYellow (show x))
did_ x = d_ x x
dv_ f = traceShowM =<< (V.freeze f)

type IMap      = IM.IntMap
type HName     = T.Text -- human readable name
type IName     = Int    -- Int name: index into bind|type vectors
type BiSubName = Int    -- index into bisubs
type IField    = Int    -- product-type fields index
type ILabel    = Int    -- sum-type labels     index
type CoreBinds = V.Vector (HName , Bind)

data VName
 = VBind IName -- bind   map
 | VArg  IName -- bisub  map
 | VExt  IName -- extern map (incl. prim instrs)

data Term -- β-reducable (possibly to a type) and type annotated
 = Var     !VName
 | Lit     Literal
 | Hole    -- to be inferred
 | App     Term [Term] -- IName [Term]
-- | PowApp  Int Term Term
 | Instr   PrimInstr
 | Coerce  Type Type
 | MultiIf [(Term , Term)] Term

 -- data constructions
 | Cons    (IM.IntMap Term)
 | Proj    Term IField
 | Label   ILabel [Expr]
 | Match   Type (IM.IntMap Expr) (Maybe Expr)
 | List    [Expr]
-- | Split   Int Expr -- eliminator: \split nArgs f → f args

-- components of our profinite distributive lattice of types
-- no β-reduce (except contained Terms)
data TyHead -- head constructors for types.
 = THVar      BiSubName  -- ix to bisubs
 | THArg      IName      -- ix to monotype env (type of the lambda-bound at ix)
-- | THArg      IName Kind -- Track rank polymorphism ({} and -> are not interchangeable)
 | THExt      IName      -- tyOf ix to externs
 | THRec      IName      -- tyOf ix to bindMap (must be guarded and covariant)

 | THSet      Uni -- | THSetFn    [Uni]
-- | THTop Kind | THBot Kind
 | THPrim     PrimType
 | THArrow    [TyContra] TyCo  -- degenerate case of THPi
 | THProd     [IField]
 | THSum      [ILabel]
 | THSplit    [ILabel]
 | THArray    TyCo

 | THPi Pi -- dependent function space. Always implicit, for explicit, write `∏(x:_) x -> Z`
 | THSi Pi (IM.IntMap Expr) -- (partial) application of pi type

 -- Families; Similar to pi/sigma, but binder is anonymous and to be 'appended' to the type
 | THRecSi IName [Term]     -- basic case when parsing a definition; also a valid CoreExpr
 | THFam Type [Type] [Expr] -- type of things it can index, and things indexing it (both can be [])

data Pi = Pi [(IName , Type)] Type -- deBruijn indexes

data TCError
 = ErrBiSub     T.Text
 | ErrTypeCheck T.Text
 | Err T.Text
  deriving Show
data Expr
 = Core     Term Type
 | CoreFn   [(IName , Type)] IS.IntSet Term Type
 | ExtFn    HName Type
 | Ty       Type
 | Fail     TCError

data Bind -- indexes in the bindmap
 = WIP
 | Checking  Type -- guard for recursive references
 | BindOK    Expr
 | BindKO -- failed to typecheck

type Type     = TyPlus
type Uni      = Int
type TyCo     = [TyHead] -- same    polarity
type TyContra = [TyHead] -- reverse polarity
type TyMinus  = [TyHead] -- input  types (lattice meet) eg. args
type TyPlus   = [TyHead] -- output types (lattice join)

-- bisubs always reference themselves, so the mu. is implicit
data BiSub = BiSub { _pSub :: [TyHead] , _mSub :: [TyHead] }
newBiSub = BiSub [] []
makeLenses ''BiSub

-- label for the different head constructors. (KAny is '_' in a way top of the entire universe)
data Kind = KPrim | KArrow | KVar | KArg | KSum | KProd | KRec | KAny
 deriving Eq

bind2Expr = \case
  BindOK e -> e

-- evaluate type application (from THIxPAp s)
tyAp :: [TyHead] -> IM.IntMap Expr -> [TyHead]
tyAp ty argMap = map go ty where
  go :: TyHead -> TyHead = \case
    THArg y -> case IM.lookup y argMap of
      Nothing -> THArg y
      Just (Ty [t]) -> t
    THArrow as ret -> THArrow (map go <$> as) (go <$> ret)
    x -> x
