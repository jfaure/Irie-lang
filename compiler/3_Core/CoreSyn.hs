-- Core Language. compiler pipeline = Text >> Parse >> Core >> STG >> SSA
{-# LANGUAGE TemplateHaskell #-}
module CoreSyn (module CoreSyn , module QName , ModIName) where
import Prim
import QName
import MixfixSyn
import Control.Lens hiding (List)
import qualified BitSetMap           as BSM
import qualified Data.Vector         as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.IntMap.Strict  as IM
import qualified Data.Map.Strict as M

global_debug = False
--global_debug = True

type ExtIName  = Int -- VExterns
type BiSubName = Int -- index into bisubs
type SrcOff    = Int -- offset into the source file
type IField    = QName
type ILabel    = QName
type TVarSet   = BitSet
type LiName    = IName -- linear names

data VName
 = VBind    IName -- name defined within this module (probably deprecate this)
 | VQBind   QName -- qualified name (modulename << moduleBits | IName)
 | VArg     IName -- introduced by lambda abstractions
 | VExt     IName -- externs; primitives, mixfixwords and imported names
 | VForeign HName -- opaque name resolved at linktime

data Term -- β-reducable (possibly to a type)
 = Var     !VName
 | Lit     !Literal
 | Question      -- attempt to infer this TT
 | Poison  !Text -- typecheck inconsistency

 | Instr   !PrimInstr
 | Cast    !BiCast Term -- it's useful to be explicit about inferred subtyping casts

 | Abs     [(IName , Type)] BitSet Term Type -- arg inames, types, freevars, term ty
 | App     Term [Term]    -- IName [Term]

 | Cons    (BSM.BitSetMap Term) -- (IM.IntMap Term)
 | Tuple   (V.Vector Term) -- Alternate version of Cons where indexes are sequential
 | TTLens  Term [IField] LensOp

 | Label   ILabel [Term] --[Expr]
 | Match   Type (BSM.BitSetMap Expr) (Maybe Expr) -- Type is the return type

 -----------------------------------------------
 -- Extra info built for/by simplification --
 -----------------------------------------------
 | Lin LiName -- Lambda-bound (may point to dup-node if bound by duped LinAbs)
 | LinAbs [(LiName , Bool , Type)] Term Type -- indicate if dups its arg

 | RecApp   Term [Term] -- direct recursion
 -- annotate where fixpoints are
 | RecLabel ILabel (V.Vector Int) [Expr]
 | RecMatch (BSM.BitSetMap (V.Vector Int , Expr)) (Maybe Expr)

 -- Named Specialised recursive fns can (mutually) recurse with themselves
 | LetSpecs [Term{-.Abs-}] Term
 | Spec IName -- spec number and the Bind it came from

 | VBruijn IName
 | BruijnAbs Int BitSet Term

 | PartialApp [Type] Term [Term] --Top level PAp => Abs (only parse generates fresh argnames)
--data LabelKind = Peano | Array Int | Tree [Int] -- indicate recurse indexes

-- lensover needs idx for extracting field (??)
data LensOp = LensGet | LensSet Expr | LensOver (ASMIdx , BiCast) Expr

type Uni     = Int  -- a universe of types
type TyMinus = Type -- input  types (lattice meet ∧) eg. args
type TyPlus  = Type -- output types (lattice join ∨)
type GroundType = [TyHead]
tyTop = TyGround []
tyBot = TyGround []

-- Theoretically TVars have their own presence in the profinite distributive lattice of types
-- The point is to pre-partition tvars since they are usually handled separately
data Pi = Pi [(IName , Type)] Type deriving Eq -- pi binder Π (x : T) → F T
data Type
 = TyGround GroundType

 -- vv tvars are temporary artefacts of inference
 | TyVar    Int -- generalizes to THBound if survives biunification and simplification
 | TyVars   BitSet GroundType

 -- vv Only occur in user type annotations
 | TyAlias  QName
 | TyTerm   Term Type       -- term should be lambda calculus or product/sum calculus
 | TyPi Pi                  -- dependent functions, implicit args (explicit as: Arg -> T)
 | TySi Pi (IM.IntMap Expr) -- Existential: some TT and a function of them (~partial app)
 | TyIndexed Type [Expr]    -- Indexed family (raw Terms can only exist here after normalisation)

-- equality of types minus dependent normalisation
instance Eq Type where
  TyGround g1 == TyGround g2 = g1 == g2
  TyVar i     == TyVar j     = i == j
  TyVars i g1 == TyVars j g2 = i == j && g1 == g2
  TyVar i     == TyVars j [] = j == (0 `setBit` i)
  TyVars j [] == TyVar i     = j == (0 `setBit` i)
  _           == _           = False

data TyCon -- Type constructors
 = THArrow    [TyMinus] TyPlus   -- degenerate case of THPi (bot -> top is the largest)
 | THTuple    (V.Vector  TyPlus) -- ordered form of THproduct
 | THProduct  (BSM.BitSetMap TyPlus)
 | THSumTy    (BSM.BitSetMap TyPlus)
 deriving Eq

-- Head constructors in the profinite distributive lattice of types
data TyHead
 = THPrim     PrimType
 | THExt      IName -- ix to builtins (use getExprType to get Type from Expr) -- rm
 | THAlias    QName
 | THSet      Uni
 | THPoison         -- marker for inconsistencies found during inference
 | THTop | THBot

 | THFieldCollision Type Type | THLabelCollision Type Type
 | THTyCon !TyCon -- BitSet cache contained tvars?

 | THBi Int Type -- Π A → F(A) polymorphic type to be instantiated on each use
 | THMu Int Type -- µx.F(x) recursive type is instantiated as Π A → A & F(A)`

 | THBound   IName  -- Π-bound tvar; instantiating Π-binder involves sub with fresh tvars
 | THMuBound IName  -- µ-bound tvar (must be guarded and covariant)
 deriving Eq

data Expr
 = Core     Term Type
 | Ty       Type
 | Set      !Int Type
 | PoisonExpr

 -- Temporary exprs for solveMixfixes; TODO should extract to new data
 | QVar     QName --(ModuleIName , IName)
 | MFExpr   Mixfixy --MFWord -- removed by solvemixfixes
 | ExprApp  Expr [Expr] -- output of solvemixfixes

--data MixfixSolved
-- = QVar     QName
-- | MFExpr   Mixfixy --MFWord -- removed by solvemixfixes
-- | ExprApp  Expr [Expr] -- output of solvemixfixes
-- | MFId     Expr

data Bind -- indexes in the bindmap
 = Queued
 | Guard  { mutuals :: [IName] , tvar :: IName } -- Inference in progress; possibly a stack of its dependencies
 -- v Marker for an inferred type waiting for generalisation (waiting for all mutual binds to be inferred)
 | Mutual { naiveExpr :: Expr , freeVs :: BitSet , recursive :: Bool , tvar :: IName , tyAnn :: Maybe Type }

 | BindKO -- failed type
 | BindOK Bool Expr -- isRec

-- | BindMutuals (V.Vector Expr)

 | BindOpt Complexity Specs Expr

type Complexity = Int -- number of Apps in the Term
type Specs      = BitSet

data ExternVar
 = ForwardRef IName -- not extern
 | Imported   Expr  -- Inlined

 | NotInScope       HName
 | NotOpened        HName HName
 | AmbiguousBinding HName -- same level binding overlap / overwrite

 | Importable ModuleIName IName -- Available externally but not obviously worth inlining
 | MixfixyVar Mixfixy           -- temp data fed to solvemixfixes

data Mixfixy = Mixfixy
 { ambigBind   :: Maybe QName
 , ambigMFWord :: [QMFWord]
 }

type ASMIdx = IName -- Field|Label-> Idx in sorted list (the actual index used at runtime)
-- Various casts inserted by inference
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

data BiSub = BiSub {
   _pSub :: Type
 , _mSub :: Type
}

makeLenses ''BiSub

-- label for the different head constructors.
data Kind = KPrim PrimType | KArrow | KSum | KProd | KRec | KAny | KBound | KTuple | KArray
 deriving (Eq , Ord)

data SrcInfo = SrcInfo Text (VU.Vector Int)
data JudgedModule = JudgedModule {
   modIName    :: IName
 , modHName    :: HName
 , nArgs       :: Int
 , bindNames   :: V.Vector HName
 , fieldNames  :: M.Map HName IName -- can we use Vector instead of Map?
 , labelNames  :: M.Map HName IName
 , judgedBinds :: V.Vector Bind
}

data OldCachedModule = OldCachedModule {
   oldModuleIName :: ModuleIName
 , oldBindNames   :: V.Vector HName -- to check if ambiguous names were deleted
} deriving Show

-- only used by prettyCore functions and the error formatter
data BindSource = BindSource {
   srcArgNames     :: V.Vector HName
 , srcBindNames    :: V.Vector HName
 , srcExtNames     :: V.Vector HName
 , srcLabelNames   :: V.Vector (V.Vector HName)
 , srcFieldNames   :: V.Vector (V.Vector HName)
 , allNames        :: V.Vector (V.Vector (HName , Expr))
}
