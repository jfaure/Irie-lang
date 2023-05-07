-- Core Language. compiler pipeline = Text >> Parse >> Core >> STG >> SSA
{-# LANGUAGE TemplateHaskell #-}
module CoreSyn (module CoreSyn , module QName , ModIName) where
import Control.Lens ( makeLenses )
import MixfixSyn ( ModIName , QMFWord )
import Prim ( Literal, PrimInstr, PrimType )
import QName
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
type IField    = Int -- QName
type ILabel    = QName
type CaseID    = Int

-- Debruijn indices vs levels
-- levels index from the bottom of the stack, eliminating the need to reindex free vars (eg. when weakening context)
-- indices eliminate the need to reindex bound variables, eg when substituting a closed expression in another context
-- Both are required for efficient β-reduction
-- locally nameless = indices for bound vars, global names for free vars.

-- Bruijns vs QBinds => QBinds are mutually in scope & Lens
data VName
 = VQBind   QName -- external qualified name (modulename << moduleBits | IName)
 | VForeign HName -- opaque name resolved at linktime
 | VLetBind QName -- + counterpart of VBruijn

data Term -- β-reducable (possibly to a type)
 = Var     !VName
 | Lit     !Literal
 | Question      -- attempt to infer this TT
 | Poison  !Text -- typecheck inconsistency

 | Instr   !PrimInstr
 | Cast    !BiCast Term -- it's useful to be explicit about inferred subtyping casts

-- ->
 | VBruijn IName
 | VBruijnLevel Int
 | BruijnAbs Int Term
 | BruijnAbsTyped Int Term [(Int , Type)] Type -- ints index arg metadata
 | App     Term [Term]    -- IName [Term]

-- {}
 | Tuple    (V.Vector Term)      -- Cartesian product
 | LetBlock (V.Vector (LetMeta , Bind))
 | LetBinds (V.Vector (LetMeta , Bind)) Term
 | TTLens  Term [IField] LensOp

-- []
 | Label   ILabel [Term]
 | CaseB   Term Type (BSM.BitSetMap Term) (Maybe Term)

-- Simplifier
 | Case CaseID Term -- term is the scrutinee. This cheapens inlining by splitting functions
 | LetSpec QName [ArgShape]
 | CaseBranches (BSM.BitSetMap Term) (Maybe Term) -- CaseB without Scrut

 | Wrap Int Term -- indicates a term was incorrectly wrapped in an abstraction (case-case simplification)
-- | CType Type -- Need to be able to embed types into some terms (but not the opposite)

-- lensover needs idx for extracting field (??)
data LensOp = LensGet | LensSet Expr | LensOver (ASMIdx , BiCast) Expr

type Uni     = Int  -- a universe of types
type TyMinus = Type -- input  types (lattice meet ∧) eg. args
type TyPlus  = Type -- output types (lattice join ∨)
type GroundType = [THead Type]
tyTop = TyGround []
tyBot = TyGround []

-- the Theory requires TVars have their own presence in the profinite distributive lattice of types
data Pi = Pi [(IName , Type)] Type deriving Eq -- pi binder Π (x : T) → F T
data Type
 = TyGround GroundType
 -- vv tvars are temporary artifacts of inference
 | TyVars   BitSet GroundType -- vars generalise to THBound if survive simplification

 -- vv User type annotations
 | TyAlias  QName
 | TyTerm   Term Type       -- term should be lambda calculus or product/sum calculus
 | TyPi Pi                  -- dependent functions, implicit args (explicit as: Arg → T)
 | TySi Pi (IM.IntMap Expr) -- Existential: some TT and a function of them (~partial app)
 | TyIndexed Type [Expr]    -- Indexed family (raw Terms can only exist here after normalisation)

tyVar v = TyVars (setBit 0 v) []
-- equality of types minus dependent normalisation
instance Eq Type where
  TyGround g1 == TyGround g2 = g1 == g2
  TyVars i g1 == TyVars j g2 = i == j && g1 == g2
  _           == _           = False

data TyCon t -- Type constructors
 = THArrow    [t] t   -- degenerate case of THPi (bot → top is the largest)
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
 | THTyCon !(TyCon ty) -- BitSet cache contained tvars?

 | THBi Int ty -- Π A → F(A) polymorphic type to be instantiated on each use
 | THMu Int ty -- µx.F(x) recursive type is instantiated as Π A → A & F(A)`
               -- recursive types must be strictly covariant (avoid curry paradox)

 | THBound   IName  -- Π-bound tvar; instantiating Π-binder involves sub with fresh tvars
 | THMuBound IName  -- µ-bound tvar (must be guarded and covariant)
 deriving (Eq , Functor , Traversable , Foldable)

data Expr
 = Core Term Type
 | Ty   Type
 | Set  !Int Type
 | PoisonExpr
 | PoisonExprWhy Text

data ArgShape
 = ShapeNone
 | ShapeLabel ILabel [ArgShape]
-- | ShapeLiteral
 | ShapeQBind QName
 | ShapeLetBind QName
 | ShapePAPLet QName [ArgShape] -- even if fully applied, it makes little difference
 deriving (Ord , Eq , Show , Generic)

data Bind
 = Queued -- Infer
 | Guard  { mutuals :: BitSet , tvar :: IName } -- being inferred; if met again, is recursive/mutual
 -- generalising mutual types must wait for all tvars to be constrained (all mutual block to be inferred)
 | Mut    { naiveExpr :: Expr , mutuals :: BitSet , letCaptured :: (Int , BitSet) , tvar :: IName }

 -- free has the atLen of all capturable vars: the reference for where the bitset bruijns are valid
 | BindOK { optLevel :: OptBind , free :: (Int , BitSet) , naiveExpr :: Expr }
 | BindUnused Text

 | WIP -- Fenv

data OptBind = OptBind
  { optId :: Int
  , bindSpecs :: M.Map [ArgShape] Term -- opt-level , specialisations
  }
optInferred = OptBind 0 mempty

data ExternVar
 = ForwardRef IName -- not extern
 | Imported   Expr  -- Inlined

 | NotInScope       HName
 | NotOpened        HName HName
 | AmbiguousBinding HName [(ModIName , IName)] -- same level binding overlap / overwrite

 | Importable ModuleIName IName -- Available externally but not obviously worth inlining
 | MixfixyVar Mixfixy           -- temp data fed to solvemixfixes

data Mixfixy = Mixfixy
 { ambigBind   :: Maybe QName -- mixfixword also bind, eg. `if_then_else_` and `then`
 , ambigMFWord :: [QMFWord]
 }

type ASMIdx = IName -- Field|Label→ Idx in sorted list (the actual index used at runtime)
-- Various casts inserted by inference
data BiCast
 = BiEQ
 | CastInstr PrimInstr
 | CastProduct Int [(ASMIdx , BiCast)] -- number of drops, and indexes into parent struct
 | CastLeaf    ASMIdx BiCast -- Lens
 | CastLeaves  [BiCast]

 | CastApp [BiCast] (Maybe [Type]) BiCast -- argcasts , maybe papcast , retcast
 | CastFnRet Int BiCast -- arg count (needed by code gen)
 | BiInst  [BiSub] BiCast -- instantiate polytypes
 | CastOver ASMIdx BiCast Expr Type

data BiSub = BiSub { _pSub :: Type , _mSub :: Type }; makeLenses ''BiSub

-- label for the different head constructors.
data Kind = KPrim PrimType | KArrow | KSum | KProd | KRec | KAny | KBound | KTuple | KArray
 deriving (Eq , Ord)

data SrcInfo = SrcInfo Text (VU.Vector Int)
data JudgedModule = JudgedModule {
   modIName   :: IName
 , modHName   :: HName
 , bindNames  :: V.Vector HName
 , labelNames :: M.Map HName IName
 , moduleTT   :: Expr
}

data OldCachedModule = OldCachedModule {
   oldModuleIName :: ModuleIName
   -- TODO preseed parse env with oldbindnames
 , oldBindNames   :: V.Vector HName -- to check if ambiguous names were deleted
} deriving Show

-- only used by prettyCore functions and the error formatter
data BindSource = BindSource {
   srcArgNames   :: V.Vector HName
 , srcBindNames  :: V.Vector HName
 , srcExtNames   :: V.Vector HName
 , srcLabelNames :: V.Vector (V.Vector HName)
 , allNames      :: V.Vector (V.Vector (HName , Expr))
}

makeBaseFunctor ''Expr
makeBaseFunctor ''Term
makeBaseFunctor ''Type
makeLenses ''Type
