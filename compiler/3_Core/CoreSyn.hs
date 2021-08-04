-- Core Language (compiler pipeline = Text >> Parse >> Core >> STG >> LLVM)

{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS  -funbox-strict-fields #-}
module CoreSyn where
import Prim
import qualified Data.Vector         as V
import qualified Data.IntMap.Strict  as IM
import Control.Lens hiding (List)

global_debug = False
--global_debug = True
d_ x   = if not global_debug then identity else let
  clYellow  x = "\x1b[33m" ++ x ++ "\x1b[0m"
  in trace (clYellow (show x))
did_ x = d_ x x
dv_ f = traceShowM =<< (V.freeze f)

type HName     = Text -- human readable name
type IName     = Int  -- Int name: index into bind|type vectors
type BiSubName = Int  -- index into bisubs
type IField    = Int  -- product-type fields
type ILabel    = Int  -- sum-type labels

data VName
 = VBind IName -- bind   map
 | VArg  IName -- bisub  map
 | VExt  IName -- extern map (incl. prim instrs)

data Term -- β-reducable (possibly to a type) and type annotated
 = Var     !VName
 | Lit     Literal
 | Hole    -- to be inferred : Bot
 | Poison  -- typecheck inconsistency

 | Abs     [(IName , Type)] IntSet Term Type -- arg inames, types, freevars, term ty
 | App     Term [Term] -- IName [Term]
 | Instr   PrimInstr

 -- data constructions
 | Cons    (IM.IntMap Term) -- convert to record
 | Label   ILabel [Expr]
 | Match   Type (IM.IntMap Expr) (Maybe Expr) -- type is the return type of this expression
 | List    [Expr]

 | TTLens  Term [IField] LensOp

data LensOp = LensGet | LensSet Expr | LensOver Expr

-- TODO improve this
-- Typemerge should be very fast
type Type     = TyPlus
type Uni      = Int
type TyMinus  = [TyHead] -- input  types (lattice meet) eg. args
type TyPlus   = [TyHead] -- output types (lattice join)

-- Head constructors in the profinite distributive lattice of types
data TyHead
 = THPrim     PrimType
 | THExt      IName -- tyOf ix to externs
 | THSet      Uni   -- Type of types
 | THPoison   -- marker for inconsistencies found during inference
 | THTop | THBot -- TODO was this problematic ?

 -- Type constructors
 | THArrow    [TyMinus] TyPlus  -- degenerate case of THPi (bot -> top is the largest fn type)
 | THTuple    (V.Vector TyPlus) -- ordered form of THproduct
 | THProduct  (IM.IntMap TyPlus)
 | THSumTy    (IM.IntMap TyPlus)
 | THArray    TyPlus

 -- Experimental
 | THVars [Int]

 -- Type variables
 | THVar       BiSubName -- generalizes to THBound if survives biunification and simplification
 | THVarGuard  IName     -- marker for vars when substituting a guarded type (mu.bound if seen again)
 | THVarLoop   IName     -- unguarded variable loops
 | THVarCircle [IName]
 | THBound     IName -- pi-bound debruijn index, (replace with fresh THVar when biunify pi binders)
 | THMuBound   IName -- mu-bound debruijn index (must be guarded and covariant) 

 -- Binders
 | THMu IName Type-- recursive type
 | THBi Int Type  -- deBruijn pi binder
 | THPi Pi        -- dependent function space. implicitly bound. (for explicit: `∏(x:_) x -> Z`)
 | THSi Pi (IM.IntMap Expr) -- (partial) application of pi type; existential

 -- type Families | indexed types
 | THRecSi IName [Term]     -- basic case when parsing a definition; also a valid CoreExpr
 | THFam Type [Type] [Expr] -- type of indexables, and things indexing it (both can be [])

data Pi = Pi [(IName , Type)] Type

-- TODO handle recursion
data QTT = QTT { _qttReads :: Int , _qttBuilds :: Int } deriving Show

data TCError
 = ErrBiSub     Text
 | ErrTypeCheck Text
 | Err Text
  deriving Show

data Expr
 = Core     Term Type
 | Ty       Type
 | Fail     TCError

data Bind -- indexes in the bindmap
 = WIP
 | Guard     { mutuals :: [IName] , args :: [IName] , tvar :: IName }
 | Mutual    { tvars :: Dominion , naiveExpr :: Expr , recursive :: Bool , tvar :: IName }

 | Checking  { mutuals :: [IName] 
             , monoMorphic :: Maybe (Dominion , Expr) -- if set, shouldn't generalise itself (request a mutual bind do it)
             , doGen :: Bool
             , recTy :: Type
             }
 | BindOK    Expr
 | BindKO -- failed typecheck -- use Poison ?

-- arrows have 2 special cases: pap and currying
--data ArrBiSub = ArrAp | ArrPAp [BiCast] | ArrCurry [BiCast]
data BiCast = BiEQ | BiCast Term | CastApp [BiCast] (Maybe [Type]) | BiInst [BiSub] BiCast | BiFail Text

-- generalisation needs to know which THVars and THArgs are dominated in a particular context
data Dominion = Dominion {
   tVarRange :: (Int , Int) -- stack of tvars
} deriving Show

data BiSub = BiSub {
   _pSub :: [TyHead]
 , _mSub :: [TyHead]
 , _pQ :: Int
 , _mQ :: Int
}

makeLenses ''BiSub
makeLenses ''QTT

-- label for the different head constructors. (KAny is '_' in a way top of the entire universe)
data Kind = KPrim | KArrow | KVar | KSum | KProd | KRec | KAny | KBound
 deriving (Eq , Ord)

-- wip module, not quite as polished as an Import module (still contains typevars and arg infos)
data JudgedModule = JudgedModule {
   bindNames   :: V.Vector HName
 , judgedBinds :: V.Vector Bind
 , typeVars    :: V.Vector BiSub
 , qtts        :: V.Vector QTT
 , argTypes    :: V.Vector BiSub
}

data BindSource = BindSource {
   srcArgNames   :: V.Vector HName
 , srcBindNames  :: V.Vector HName
 , srcExtNames   :: V.Vector HName
 , srcLabelNames :: V.Vector HName
 , srcFieldNames :: V.Vector HName
}
