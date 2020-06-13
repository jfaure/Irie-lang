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

data Term -- Codegennable - all other datas are typing artefacts
 = Var     VName
 | Lit     Literal
 | App     Term    [Term] -- IName [Term]
 | MultiIf [(Term , Term)] Term
 | Instr   PrimInstr

 -- data constructions
 | Cons    (M.Map IField Term)
 | Proj    Term IField
 | Label   ILabel [Expr]
 | Match   (M.Map ILabel Expr) (Maybe Term)
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
 | THArg      IName      -- ix to monotype env (type of the lambda-bound at ix)
 | THAlias    IName      -- ix to bindings
 | THExt      IName      -- ix to externs

 | THPrim     PrimType
 | THSet      Uni
 | THArrow    [TyContra] TyCo
 | THRec      IName -- must be guarded (by other TyHead)
 | THProd     (M.Map IField TyCo) -- dependent record
 | THSum      (M.Map ILabel TyCo) -- map of function types
 | THArray    TyCo

-- | THSelfIx   IName -- only valid in dependent record
-- partial application in dependent function space
 | THPi [(IName , Type)] Type (M.Map IName Expr)
 | THSi [(IName , Type)] Type (M.Map IName Expr)
 | THEQ LC LC -- proof term

-- | THQ PiSigma [(IName , Type)] Type (M.Map IName Expr) data PiSigma = Pi | Sigma
 | THULC LC
 | THInstr PrimTyInstr [IName] -- pretty much only in THPi
 | THRecApp IName [Expr]
 | THLamBound IName

-- | THJoin [TyHead]
-- | THMeet [TyHead]
-- | THTop Kind
-- | THBot Kind

-- eliminator: split t with (x , y) → u
-- deconstructs the scrutinee t, binding its components to x and y, and then evaluates u.

-- label for the different head constructors
data Kind = KPrim | KArrow | KVar | KSum | KProd | KAny | KRec
  deriving Eq

data Pi = Pi [(IName , Type)] Expr
data Expr
 = Core    Term Type
 | Ty      Type  -- Set0
 | ULC     LC    -- poly-universe lambda calculus
 | Fn      Pi
 | ExprPAp Pi (IMap Expr)

data LC -- poly-universe lambda calculus eg. `f a b = a (b b)`
 = LCArg   IName
 | LCLabel IName
 | LCRec   IName -- index into bindmap (whose type is often not immediately known)
 | LCApp   LC LC
 | LCPow   Int LC LC  -- power app
 | LCTerm  Term Type  -- terms can be args to types and exprs

data Bind -- indexes in the bindmap
 = WIP
 | Checking  Type -- guard for recursive references
 | BindOK [IName] Expr
-- | BindOK Expr
 | BindKO -- failed to typecheck

bind2Expr = \case
  BindOK _ e -> e

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
