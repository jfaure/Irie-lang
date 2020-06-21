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
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import Control.Lens hiding (List)
import Data.List (intercalate)

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
type CoreBinds = V.Vector Bind

data VName
 = VBind IName -- bind   map
 | VArg  IName -- bisub  map
 | VExt  IName -- extern map (incl. prim instrs)

data Term -- β-reducable (possibly to a type) and type annotated
 = Var     !VName  -- {-# UNPACK #-} 
 | Lit     Literal
 | Hole    -- to be inferred
 | App     Term [Term] -- IName [Term]
-- | Pow     Int Term Term
 | Instr   PrimInstr
 | Coerce  Type Type
 | MultiIf [(Term , Term)] Term

 -- data constructions
 | Cons    (M.Map IField Term)
 | Proj    Term IField
 | Label   ILabel [Expr]
 | Match   (M.Map ILabel Expr) (Maybe Expr)
 | List    [Expr]
 | Split   Int Expr -- eliminator: \split nArgs f → f args

-- components of our profinite distributive lattice of types
-- unless explicit annotation, assume type Set0
-- no β-reduce (except contained Terms)
data TyHead -- head constructors for types.
 = THVar      BiSubName  -- ix to bisubs
 | THArg      IName      -- ix to monotype env (type of the lambda-bound at ix)
 | THExt      IName      -- tyOf ix to externs
 | THRec      IName      -- tyOf ix to bindMap (must be guarded and covariant)
 | THTyRec    IName      -- ix to bindMap (is a type)

 | THSet      Uni -- | THSetFn    [Uni]
 | THTop Kind | THBot Kind
 | THPrim     PrimType
 | THArrow    [TyContra] TyCo  -- degenerate case of THPi
 | THProd     [IField]
 | THSum      [ILabel]
 | THArray    TyCo

 | THPi Pi -- dependent function space
 | THSi Pi (M.Map IName Expr) -- (partial) application of pi type
 | THRecSi IName [Term] -- application (ie. of indexed family)
 | THSub Type Type -- indexed families are lists of subtype definitions

data Pi = Pi [(IName , Type)] Type -- deBruijn indexes

data Expr
 = Core   Term Type
 | CoreFn [IName] Term Type
 | Ty     Type

data Bind -- indexes in the bindmap
 = WIP
 | Checking  Type -- guard for recursive references
 | BindOK    Expr
 | BindKO -- failed to typecheck

--data LC -- typeable in Setn (ie. type is Seta -> Set b -> Set c)
-- = LCArg   IName
-- | LCApp   LC LC
-- | LCPow   Int LC LC  -- power app
-- | LCIx    LC (Term , Type)
--
-- | LCRec   IName -- index into bindmap (whose type is often not immediately known)
-- | LCLabel IName
-- | LCExt   IName

type Type     = TyPlus
type Uni      = Int
type TyCo     = [TyHead] -- same    polarity
type TyContra = [TyHead] -- reverse polarity
type TyMinus  = [TyHead] -- input  types (lattice meet) eg. args
type TyPlus   = [TyHead] -- output types (lattice join)

-- bisubs always reference themselves, so the mu. is implicit
data BiSub = BiSub { _pSub :: [TyHead] , _mSub :: [TyHead] }
newBiSub = BiSub [] []

-- label for the different head constructors. (KAny is the top of the entire universe)
data Kind = KPrim | KArrow | KVar | KArg | KSum | KProd | KRec | KAny
  deriving Eq

bind2Expr = \case
  BindOK e -> e

makeLenses ''BiSub

-- evaluate type application (from THIxPAp s)
tyAp :: [TyHead] -> M.Map IName Expr -> [TyHead]
tyAp ty argMap = map go ty where
  go :: TyHead -> TyHead = \case
    THArg y -> case M.lookup y argMap of
      Nothing -> THArg y
      Just (Ty [t]) -> t
    THArrow as ret -> THArrow (map go <$> as) (go <$> ret)
    x -> x
