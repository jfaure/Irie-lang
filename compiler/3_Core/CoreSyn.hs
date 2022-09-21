-- Core Language. compiler pipeline = Text >> Parse >> Core >> STG >> SSA
{-# LANGUAGE TemplateHaskell , TypeFamilies #-}
module CoreSyn (module CoreSyn , module QName , ModIName) where
import Control.Lens ( makeLenses )
import MixfixSyn ( ModIName, QMFWord )
import Prim ( Literal, PrimInstr, PrimType )
import QName ( fieldBit, labelBit, maxIName, maxModuleName, mkQName, modName, moduleBits, qName2Key, unQName, QName(..) )
import qualified BitSetMap as BSM ( BitSetMap )
import qualified Data.IntMap.Strict as IM ( IntMap )
import qualified Data.Map.Strict as M ( Map )
import qualified Data.Vector as V ( Vector )
import qualified Data.Vector.Unboxed as VU ( Vector )
import Data.Functor.Foldable.TH (makeBaseFunctor)

global_debug = False

type ExtIName  = Int -- VExterns
type BiSubName = Int -- index into bisubs
type SrcOff    = Int -- offset into the source file
type IField    = QName
type ILabel    = QName
type TVarSet   = BitSet

-- LiName
-- * explicit dup nodes ⇒ function args may be duped
-- * mark let-bounds start,end , recursive and mutuals
-- ? different dups in different case-branches ⇒ defer until branch known (potentially duped / dropped linames)
-- ? dependency graph = LetScope ModIName
-- ? open record
-- 0. Module = \.. ⇒ let .. in exportlist (functor might be const)
-- 1. Parse finds arg binds and uniquely names everything else as Extern
-- 2. Resolve scope: scopeBitset → IName → LiTable LiName
type LiName  = QName -- ! The modIName indicates amount of dups
type LiTable = V.Vector VName
type CaseID = Int
type BranchID = Int

data VName
 = VArg     IName -- introduced by lambda abstractions
 | VQBind   QName -- qualified name (modulename << moduleBits | IName)
 | VExt     IName -- forward references, primitives, imported names (incl mixfixwords)
 | VForeign HName -- opaque name resolved at linktime

data Lam = Lam [(IName , Type)] BitSet Type -- arg inames, types, freevars, term, ty
type ABS = (Lam , Term)

-- for makeBaseFunctor to work we must make the fixpoints obvious: No mutual recursion
data Term -- β-reducable (possibly to a type)
 = Var     !VName
 | Lit     !Literal
 | Question      -- attempt to infer this TT
 | Poison  !Text -- typecheck inconsistency

 | Instr   !PrimInstr
 | Cast    !BiCast Term -- it's useful to be explicit about inferred subtyping casts

 | Abs     ABS
 | App     Term [Term]    -- IName [Term]

 | Prod    (BSM.BitSetMap Term) -- (IM.IntMap Term)
 | Tuple   (V.Vector Term)      -- Alternate version of Cons where indexes are sequential
 | TTLens  Term [IField] LensOp

 | Label   ILabel [Term] --[Expr]
 | Match   Term Type (BSM.BitSetMap ABS) (Maybe ABS)

 -----------------------------------------------
 -- Extra info built for/by simplification --
 -----------------------------------------------
 | Case CaseID Term -- term is the scrutinee. This makes inlining very cheap

 | Lin LiName -- Lambda-bound (may point to dup-node if bound by duped LinAbs)
 | LinAbs [(LiName , Bool , Type)] Term Type -- indicate if dups its arg

 | RecApp   Term [Term] -- direct recursion

 -- Named Specialised recursive fns can (mutually) recurse with themselves
 | LetSpecs [Term{-.Abs-}] Term
 | Spec QName -- mod = bind it came from , unQ = spec number

 -- Used to make new functions internally (esp. specialisations)
 | VBruijn IName
 | BruijnAbs Int BitSet Term

 | PartialApp [Type] Term [Term] --Top level PAp ⇒ Abs (only parse generates fresh argnames)
--data LabelKind = Peano | Array Int | Tree [Int] -- indicate recurse indexes

-- lensover needs idx for extracting field (??)
data LensOp = LensGet | LensSet Expr | LensOver (ASMIdx , BiCast) Expr

type Uni     = Int  -- a universe of types
type TyMinus = Type -- input  types (lattice meet ∧) eg. args
type TyPlus  = Type -- output types (lattice join ∨)
type GroundType = [THead Type]
tyTop = TyGround []
tyBot = TyGround []

-- Theoretically TVars have their own presence in the profinite distributive lattice of types
-- The point is to pre-partition tvars since they are usually handled separately
data Pi = Pi [(IName , Type)] Type deriving Eq -- pi binder Π (x : T) → F T
data Type
 = TyGround GroundType

 -- vv tvars are temporary artifacts of inference
 | TyVar    Int -- generalizes to THBound if survives biunification and simplification
 | TyVars   BitSet GroundType

 -- vv Only occur in user type annotations
 | TyAlias  QName
 | TyTerm   Term Type       -- term should be lambda calculus or product/sum calculus
 | TyPi Pi                  -- dependent functions, implicit args (explicit as: Arg → T)
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

data TyCon t -- Type constructors
 = THArrow    [TyMinus] t   -- degenerate case of THPi (bot → top is the largest)
 | THTuple    (V.Vector t) -- ordered form of THproduct
 | THProduct  (BSM.BitSetMap t)
 | THSumTy    (BSM.BitSetMap t)
 | THSumOpen  (BSM.BitSetMap t) t -- [li : τi | (lj : pj for lj ∉ li)]
 deriving (Eq , Functor , Foldable , Traversable)

-- Head constructors in the profinite distributive lattice of types
type TyHead = THead Type
data THead ty
 = THPrim     PrimType
 | THExt      IName -- ix to builtins (use getExprType to get Type from Expr) -- rm
 | THAlias    QName
 | THSet      Uni
 | THPoison         -- marker for inconsistencies found during inference
 | THTop | THBot

 | THFieldCollision ty ty | THLabelCollision ty ty
 | THTyCon !(TyCon Type) -- BitSet cache contained tvars?

 | THBi Int ty -- Π A → F(A) polymorphic type to be instantiated on each use
 | THMu Int ty -- µx.F(x) recursive type is instantiated as Π A → A & F(A)`
               -- recursive types must be strictly covariant (avoid curry paradox)

 | THBound   IName  -- Π-bound tvar; instantiating Π-binder involves sub with fresh tvars
 | THMuBound IName  -- µ-bound tvar (must be guarded and covariant)
 deriving (Eq , Functor , Traversable , Foldable)

data Expr
 = Core     Term Type
 | Ty       Type
 | Set      !Int Type
 | PoisonExpr

 -- Temporary exprs for solveMixfixes; TODO should extract to new data
 | QVar     QName
 | MFExpr   Mixfixy
 | ExprApp  Expr [Expr] -- output of solvemixfixes

--data MixfixSolved
-- = QVar     QName
-- | MFExpr   Mixfixy --MFWord -- removed by solvemixfixes
-- | ExprApp  Expr [Expr] -- output of solvemixfixes
-- | MFId     Expr

data Bind -- elements of the bindmap
 = Queued
 | Guard  { mutuals ∷ BitSet , tvar ∷ IName } -- marker for stacking inference - if met again, its recursive/mutual
 -- | Marker for an inferred type waiting for generalisation (waiting for all mutual binds to be inferred)
 | Mutual { naiveExpr ∷ Expr , freeVs ∷ BitSet , recursive ∷ Bool , tvar ∷ IName , tyAnn ∷ Maybe Type }

-- | Function already partially generalised, must be re-generalised once all free-vars are resolved
-- | LetBound { recursive ∷ Bool , naiveExpr ∷ Expr }
 | BindKO -- failed type inference
 | BindOK { optLevel ∷ Int , letBound ∷ Bool , recursive ∷ Bool , naiveExpr ∷ Expr } -- isRec

-- | BindMutuals (V.Vector Expr)

 | BindOpt Complexity Specs Expr

type Complexity = Int -- number of Apps in the Term
type Specs      = BitSet

data ExternVar
 = ForwardRef IName -- not extern
 | Imported   Expr  -- Inlined

 | NotInScope       HName
 | NotOpened        HName HName
 | AmbiguousBinding HName [(ModIName , IName)] -- same level binding overlap / overwrite

 | Importable ModuleIName IName -- Available externally but not obviously worth inlining
 | MixfixyVar Mixfixy           -- temp data fed to solvemixfixes

data Mixfixy = Mixfixy
 { ambigBind   ∷ Maybe QName -- mixfixwords can also be standalone bindings, eg. `if_then_else_` and `then`
 , ambigMFWord ∷ [QMFWord]
 }

type ASMIdx = IName -- Field|Label→ Idx in sorted list (the actual index used at runtime)
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

data BiSub = BiSub {
   _pSub ∷ Type
 , _mSub ∷ Type
}; makeLenses ''BiSub

-- label for the different head constructors.
data Kind = KPrim PrimType | KArrow | KSum | KProd | KRec | KAny | KBound | KTuple | KArray
 deriving (Eq , Ord)

data SrcInfo = SrcInfo Text (VU.Vector Int)
data JudgedModule = JudgedModule {
   modIName    ∷ IName
 , modHName    ∷ HName
 , nArgs       ∷ Int
 , bindNames   ∷ V.Vector HName
 , fieldNames  ∷ M.Map HName IName -- can we use Vector instead of Map?
 , labelNames  ∷ M.Map HName IName
 , judgedBinds ∷ V.Vector Bind
 , specs       ∷ Maybe Specialisations
}

type FnSize = Bool -- <=? 1 App
data Specialisations = Specialisations { specBinds ∷ V.Vector (FnSize , Term) , specsCache ∷ V.Vector (M.Map [ArgShape] IName) }

data ArgShape
 = ShapeNone
 | ShapeLabel ILabel [ArgShape]
 | ShapeQBind QName
 deriving (Ord , Eq , Show , Generic)

--emptyJudgedModule iNm hNm = JudgedModule iNm hNm 0 mempty mempty mempty mempty

data OldCachedModule = OldCachedModule {
   oldModuleIName ∷ ModuleIName
 , oldBindNames   ∷ V.Vector HName -- to check if ambiguous names were deleted
} deriving Show

-- only used by prettyCore functions and the error formatter
data BindSource = BindSource {
   srcArgNames     ∷ V.Vector HName
 , srcBindNames    ∷ V.Vector HName
 , srcExtNames     ∷ V.Vector HName
 , srcLabelNames   ∷ V.Vector (V.Vector HName)
 , srcFieldNames   ∷ V.Vector (V.Vector HName)
 , allNames        ∷ V.Vector (V.Vector (HName , Expr))
}

makeBaseFunctor ''Expr
makeBaseFunctor ''Term
makeBaseFunctor ''Type
