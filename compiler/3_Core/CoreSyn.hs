-- Core Language (compiler pipeline = Text >> Parse >> Core >> STG >> LLVM)
{-# LANGUAGE TemplateHaskell #-}
module CoreSyn where
import Prim
import qualified Data.Vector         as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.IntMap.Strict  as IM
import qualified Data.Map as M
import Control.Lens hiding (List)
import MixfixSyn

--global_debug = False
global_debug = True
d_ x   = let --if not global_debug then identity else let
  clYellow  x = "\x1b[33m" ++ x ++ "\x1b[0m"
  in trace (clYellow (show x))
did_ x = d_ x x
dv_ f = traceShowM =<< (V.freeze f)

-- INames are indexes into the main bindings vector
type ExtIName    = Int  -- VExterns
type BiSubName   = Int  -- index into bisubs
type IField      = Int  -- product-type fields
type ILabel      = Int  -- sum-type labels
type SrcOff      = Int  -- offset into the source file
type Complexity  = Int  -- number of Apps in the Term

data VName
 = VBind   IName
 | VQBind  ModuleIName IName
 | VArg    IName
 | VExt    IName -- extern map (incl. prim instrs and mixfixwords)

data Term -- β-reducable (possibly to a type) and type annotated
 = Var     !VName
 | Lit     !Literal
 | Question      -- attempt to infer this TT
 | Poison  !Text -- typecheck inconsistency

 | Instr   !PrimInstr
 | Cast    !BiCast Term -- it's useful to be explicit about inferred subtyping casts

 | Abs     [(IName , Type)] IntSet Term Type -- arg inames, types, freevars, term ty
 | Hole     -- argument hole (part of an implicit Abs)
 | App     Term [Term]    -- IName [Term]
 | PartialApp [Type] Term [Term] -- only built by the simplifier
 -- Top level PAp => Abs (we can only produce new names during parse)

 | Cons    (IM.IntMap Term)
 | TTLens  Term [IField] LensOp

 | Label   ILabel [Expr]
 | Match   Type (IM.IntMap Expr) (Maybe Expr) -- type is the return type of this expression

 | List    [Expr]

data LensOp = LensGet | LensSet Expr | LensOver (ASMIdx , BiCast) Expr -- lensover needs a lens for extracting field

-- TODO improve this ; Typemerge should be very fast
type Type     = TyPlus
type Uni      = Int
type TyMinus  = [TyHead] -- input  types (lattice meet) eg. args
type TyPlus   = [TyHead] -- output types (lattice join)
holeTy        = []

data TyCon -- Type constructors
 = THArrow    [TyMinus] TyPlus -- degenerate case of THPi (bot -> top is the largest)
 | THTuple    (V.Vector  TyPlus) -- ordered form of THproduct
 | THProduct  (IntMap TyPlus)
 | THSumTy    (IntMap TyPlus)
 | THArray    TyPlus

-- Head constructors in the profinite distributive lattice of types
data TyHead
 = THPrim     PrimType
 | THExt      IName -- tyOf ix to externs
 | THSet      Uni   -- Type of types
 | THPoison   -- marker for inconsistencies found during inference
 | THTop | THBot

 | THFieldCollision Type Type
 | THTyCon !TyCon

 -- Binders
 | THMu IName Type-- recursive type
 | THBi Int Type  -- deBruijn pi binder
 | THPi Pi        -- dependent function space. implicitly bound. (for explicit: `∏(x:_) x -> Z`)
 | THSi Pi (IM.IntMap Expr) -- (partial) application of pi type; existential

 -- Type variables
 | THVars      IntSet
 | THVar       BiSubName -- generalizes to THBound if survives biunification and simplification
 | THVarGuard  IName     -- mark vars when substituting a guarded type (mu.bound if seen again)
 | THVarLoop   IName     -- unguarded variable loops
 | THBound     IName     -- pi-bound debruijn index, (replace with fresh THVar when biunify pi binders)
 | THMuBound   IName     -- mu-bound debruijn index (must be guarded and covariant) 

 -- type Families | indexed types
 | THRecSi IName [Term]     -- basic case when parsing a definition; also a valid CoreExpr
 | THFam Type [Type] [Expr] -- type of indexables, and things indexing it (both can be [])

data Pi = Pi [(IName , Type)] Type

-- TODO handle recursion
--data QTT = QTT { _qttReads :: Int , _qttBuilds :: Int } deriving Show
data TmpBiSubError = TmpBiSubError { msg :: Text , got :: Type , expected :: Type }
data BiSubError = BiSubError SrcOff TmpBiSubError
data ScopeError
  = ScopeError Text
  | AmbigBind  Text
data TCErrors = TCErrors [ScopeError] [BiSubError]

data Expr
 = Core     Term Type
 | Ty       Type
 | Set      !Int Type
 | PoisonExpr

 -- Temporary exprs for solveMixfixes; TODO should make new data
 | QVar     (ModuleIName , IName)
 | MFExpr   Mixfixy --MFWord -- removed by solvemixfixes
 | ExprApp  Expr [Expr] -- output of solvemixfixes
 | Fail     Text -- TCError

data Bind -- indexes in the bindmap
 = WIP
 | Guard     { mutuals :: [IName] , args :: [IName] , tvar :: IName }
 | Mutual    { tvars :: Dominion , naiveExpr :: Expr , recursive :: Bool , tvar :: IName }

 | Checking  { mutuals :: [IName] 
             , monoMorphic :: Maybe (Dominion , Expr) -- if set, shouldn't generalise itself (ask (the first seen) mutual bind do it)
             , doGen :: Bool
             , recTy :: Type
             }
 | BindKO -- failed typecheck
 | BindOK    Expr
 | BindOpt   Complexity Expr -- optimized binding

-- mixfixWords :: [MFWord]
-- hNameMFWords :: M.Map HName [MFIName]
data ExternVar
 = ForwardRef IName -- not extern
 | Imported   Expr

 | NotInScope       HName
 | AmbiguousBinding HName -- bindings overlap not allowed

 | Importable ModuleIName IName -- read allBinds
 | MixfixyVar Mixfixy -- for solvemixfixes
data Mixfixy = Mixfixy
 { ambigBind   :: Maybe (ModuleIName , IName)
 , ambigMFWord :: [QMFWord] --[(ModuleIName , [QMFWord])]
 }

type ASMIdx = IName -- Field|Label-> Idx in sorted list (the actual index used at runtime)
data BiCast
 = BiEQ
 | CastInstr PrimInstr
 | CastProduct Int [(ASMIdx , BiCast)] -- number of drops, and indexes into the parent struct
 | CastLeaf    ASMIdx BiCast -- Lens
 | CastLeaves  [BiCast]

 | CastApp [BiCast] (Maybe [Type]) BiCast -- argcasts , maybe papcast , retcast
 | CastFnRet Int BiCast -- arg count (needed by code gen)
 | BiInst  [BiSub] BiCast -- instantiate polytypes
 | CastOver ASMIdx BiCast Expr Type

-- | CastFn {- cast for fn arg -} BiCast Expr Type -- used by lensOver to "cast" records
-- | BiFail Text
-- | CastSequence [BiCast]
-- | BiCast Term

-- generalisation needs to know which THVars and THArgs are dominated in a particular context
data Dominion = Dominion {
   tVarRange :: (Int , Int) -- stack of tvars
} deriving Show

data BiSub = BiSub {
   _pSub :: [TyHead]
 , _mSub :: [TyHead]
 , _pQ   :: Int
 , _mQ   :: Int
}

makeLenses ''BiSub
--makeLenses ''QTT

-- label for the different head constructors. (KAny is in a way top of the entire universe)
data Kind = KPrim | KArrow | KVar | KSum | KProd | KRec | KAny | KBound | KTuple | KArray
 deriving (Eq , Ord)

data SrcInfo = SrcInfo Text (VU.Vector Int)
data JudgedModule = JudgedModule {
   modName     :: HName
-- , fileDeps    :: [HName]
 , bindNames   :: V.Vector HName
 , fieldNames  :: M.Map HName IName
 , labelNames  :: M.Map HName IName
 , judgedBinds :: V.Vector Bind
}

data BindSource = BindSource {
   srcArgNames   :: V.Vector HName
 , srcBindNames  :: V.Vector HName
 , srcExtNames   :: V.Vector HName
 , srcLabelNames :: V.Vector HName
 , srcFieldNames :: V.Vector HName
}
