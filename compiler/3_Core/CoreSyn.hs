-- Core Language (compiler pipeline = Text >> Parse >> Core >> STG >> LLVM)

{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS  -funbox-strict-fields #-}
module CoreSyn where
import Prim
import qualified Data.Vector         as V
import qualified Data.IntMap.Strict  as IM
--import qualified Data.IntSet         as IS
import Control.Lens hiding (List)

d_ x   = let
  clYellow  x = "\x1b[33m" ++ x ++ "\x1b[0m"
  in trace (clYellow (show x))
did_ x = d_ x x
dv_ f = traceShowM =<< (V.freeze f)

type IMap      = IM.IntMap
type HName     = Text -- human readable name
type IName     = Int    -- Int name: index into bind|type vectors
type BiSubName = Int    -- index into bisubs
type IField    = Int    -- product-type fields index
type ILabel    = Int    -- sum-type labels     index

data VName
 = VBind IName -- bind   map
 | VArg  IName -- bisub  map
 | VExt  IName -- extern map (incl. prim instrs)

data Term -- β-reducable (possibly to a type) and type annotated
 = Var     !VName
 | Lit     Literal
 | Hole    -- to be inferred
 | Poison  -- didn't typecheck

 | Abs     [(IName , Type)] IntSet Term Type -- arg inames, types, freevars, term ty
 | App     Term [Term] -- IName [Term]
 | Instr   PrimInstr

 -- data constructions
 | Cons    (IM.IntMap Term) -- convert to record
 | Proj    Term IField
 | Label   ILabel [Expr]
 | Match   Type (IM.IntMap Expr) (Maybe Expr)
 | List    [Expr]
 | TTLens  Term [IField] LensOp

-- | Coerce  Type Type
-- | Split   Int Expr -- eliminator: \split nArgs f → f args

data LensOp = LensGet | LensSet Expr | LensOver Expr

-- Head constructors in the profinite distributive lattice of types
data TyHead
 = THVar      BiSubName  -- ix to bisubs; temp type variable that generalizes to THBound if survives biunification
 | THBound    IName      -- generalized THVar (pi-bound debruijn index) (note. make new THVars to biunify pi binders)
 | THArg      IName      -- ix to monotype env (type of a lambda-bound)
 | THRec      IName      -- tyOf ix to bindMap (must be guarded and covariant) placeholder while checking binding
 | THExt      IName      -- tyOf ix to externs

 | THSet      Uni
 | THPrim     PrimType
 | THArrow    [TyMinus] TyPlus -- degenerate case of THPi
 | THTuple    [TyPlus]         -- possibly unnecessary

 | THProduct  (IM.IntMap TyPlus)
 | THSumty    (IM.IntMap [TyPlus])

-- | THProd     [IField]
 | THSum      [ILabel]
 | THSplit    [ILabel]

 | THArray    TyPlus

 -- when is binder implicit ?
 | THBi Int Type                 -- deBruijn pi binder
-- | THBiElim (V.Vector Type) Type -- no need to eagerly substitute typevars

 | THPi Pi -- dependent function space. Always implicit, for explicit, write `∏(x:_) x -> Z`
 | THSi Pi (IM.IntMap Expr) -- (partial) application of pi type

 -- type Families | indexed types
 | THRecSi IName [Term]     -- basic case when parsing a definition; also a valid CoreExpr
 | THFam Type [Type] [Expr] -- type of things it can index, and things indexing it (both can be [])
  -- | THSetFn    [Uni] | THTop Kind | THBot Kind

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
 | Checking  { mutuals :: [IName] 
             , monoMorphic :: Maybe (Dominion , Expr) -- if set, shouldn't generalise itself (request a mutual bind do so)
             , doGen :: Bool
             , recTy :: Type
             }
 | BindOK    Expr
 | BindKO -- failed to typecheck

type Type     = TyPlus
type Uni      = Int
type TyMinus  = [TyHead] -- input  types (lattice meet) eg. args
type TyPlus   = [TyHead] -- output types (lattice join)

-- arrows have 2 special cases: pap and currying
--data ArrBiSub = ArrAp | ArrPAp [BiCast] | ArrCurry [BiCast]
data BiCast = BiEQ | BiCast Term | CastApp [BiCast] (Maybe [Type]) | BiInst [BiSub] BiCast | BiFail Text

-- generalisation needs to know which THVars and THArgs are dominated in a particular context
data Dominion = Dominion {
   tVarRange :: (Int , Int) -- stack of tvars
} deriving Show

-- bisubs always reference themselves, so the initial mu. is implicit
data BiSub = BiSub {
   _pSub :: [TyHead]
 , _mSub :: [TyHead]
}

makeLenses ''BiSub
makeLenses ''QTT

-- label for the different head constructors. (KAny is '_' in a way top of the entire universe)
data Kind = KPrim | KArrow | KVar | KArg | KSum | KProd | KRec | KAny
 deriving Eq

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
