-- Core Language. compiler pipeline = Text >> Parse >> Infer >> Simplify >> Asm
{-# LANGUAGE TemplateHaskell #-}
module CoreSyn (module CoreSyn , module QName , ModIName) where
import Control.Lens ( makeLenses )
import MixfixSyn ( ModIName , QMFWord )
import Prim ( Literal, PrimInstr, PrimType )
import QName
import qualified BitSetMap as BSM ( BitSetMap )
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
-- Note. lifted let binds are appended to the module and become VQBinds
-- (qualified IName -> bind index) obtained via Externs.iNameToBindName: (topBinds : BitSet) -> QName -> Int
newtype VName = VQBindIndex QName
data LetMeta = LetMeta { isTop :: Bool , letIName :: QName , letBindIndex :: VName , srcLoc :: Int }

data Term -- β-reducable (possibly to a type)
 = Var !VName -- Direct index into modBinds rather than a qualified IName
 | Lit     !Literal
 | Question      -- attempt to infer this TT
 | Poison  !Text -- typecheck inconsistency
 | Instr   !PrimInstr
 | X86Intrinsic Text
 | Cast    !BiCast Term -- it's useful to be explicit about inferred subtyping casts

-- ->
 | VBruijn IName
 | VBruijnLevel Int
 | BruijnAbs Int Term
 | BruijnAbsTyped Int Term [(Int , Type)] Type -- ints index arg metadata
 | App     Term [Term]
 | Captures VName -- rec/mut: Read bind and app its captures, can't know them in one pass
-- | BruijnCaptures Int BitSet Term

-- {}
 | Array    (V.Vector Term) -- All have same type
 | Tuple    (V.Vector Term)
 | Prod     (BSM.BitSetMap Term)
 | LetBinds (V.Vector (LetMeta , Bind)) Term -- change to Lets bitset (lets are lifted now)
 | Lets BitSet Term
 | TTLens  Term [IField] LensOp

-- []
 | Label   ILabel [Term]
 | CaseB   Term Type (BSM.BitSetMap Term) (Maybe Term)
 | CaseSeq Int Term Type (BSM.BitSetMap Term) (Maybe Term)

-- Simplifier
 | LetSpec QName [ArgShape]
 | Skip Term

 | Ty Type -- to embed (TermF Type): `-> {} [] let-in` may contain types

-- Π types are "normal" term functions
-- | Ty2 Type2
 | SigmaApp Term Term -- basically a PAp (no immediate β-reduction)
 | Meet Term Term | Join Term Term -- ^ v lattice operators
 | Mu Int Term -- deBruijn variable is marked as a fixpoint
-- factorial = fix (\rec n -> if n <= 1 then 1 else n * rec (n-1)) 5
-- squishTree : fix b [Node (A , fix C [Cons (b , c) | Nil])] -> d -> fix d [Cons (A , d)]
type TInt = Int -- index into thead & flow vectors
type Type2 = TyCon TInt -- tree branches are indices into THead & tvar vectors
type FlowVec  = V.Vector (BitSet , BitSet) -- + - flow edges
type THeadVec = V.Vector (THead Int) -- tycons?
-- ? Instantiation: Term -> Type2 ; (VBruijn -> TInt)
-- ? Generalisation: Type2 -> Term
-- ? Checking: ([Type2 | Term] <:? Term) -> Term
-- - handle better (label <-> function) types isomorphism

-- lensover needs idx for extracting field (??)
data LensOp = LensGet | LensSet Expr | LensOver (ASMIdx , BiCast) Expr

type Uni     = Int  -- a universe of types
type TyMinus = Type -- input  types (lattice meet ∧) eg. args
type TyPlus  = Type -- output types (lattice join ∨)
type GroundType = [THead Type]
tyTop = TyGround []
tyBot = TyGround []

data Type
 = TyGround GroundType
 | TyVars   BitSet GroundType -- tvars are temp artefacts of inference: generalise to THBound if survive simplification

data TyCon t -- Type constructors
 = THArrow    [t] t   -- degenerate case of THPi (bot → top is the largest)
 | THTuple    (V.Vector t) -- ordered form of THproduct
 | THArray    t
 | THProduct  (BSM.BitSetMap t)
 | THSumTy    (BSM.BitSetMap t)
 | THSumOpen  (BSM.BitSetMap t) -- [li : τi | (lj : pj for lj ∉ li)]
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

 | THBound   IName  -- Π-bound tvar; instantiating Π-binder involves sub with fresh tvars
 | THMuBound IName  -- µ-bound tvar; semantically identical to THBound (must be guarded and covariant)
 deriving (Eq , Functor , Traversable , Foldable)

tyVar v = TyVars (setBit 0 v) []
-- equality of types minus dependent normalisation
instance Eq Type where -- To union/intersect THeads ...
  TyGround g1 == TyGround g2 = g1 == g2
  TyVars i g1 == TyVars j g2 = i == j && g1 == g2
  _           == _           = False

data Expr = Core { exprTerm :: Term , exprType :: Type }
tySet l = TyGround [THSet l]
ty t = Core (Ty t) (tySet 0)
poisonExpr = Core (Poison "") tyTop -- TODO top or bot? (they're defined the same atm)

data ArgShape
 = ShapeNone
 | ShapeLabel ILabel [ArgShape]
-- | ShapeLiteral Literal
 | ShapeQBind QName
 | ShapeLetBind QName
 | ShapePAPLet QName [ArgShape] -- even if fully applied, it makes little difference
 deriving (Ord , Eq , Show , Generic)

data Bind
 = Guard  { tvar :: IName } -- being inferred; if met again, is recursive/mutual
 -- generalising mutual types must wait for all tvars to be constrained (all mutual block to be inferred)
 | Mutu Expr BitSet IName -- tvarIdx
 | BindOK { optLevel :: OptBind , bindToExpr :: Expr }
 | BindRenameCaptures Int BitSet Expr -- atLen and freeVars bitset (@ the atLen)

data OptBind = OptBind
  { optId :: Int
  , bindSpecs :: M.Map [ArgShape] Term -- opt-level , specialisations
--  , doAsm :: Bool -- iff more primitives than type constructor operations & is used
  }
optInferred = OptBind 0 mempty

data ExternVar
 = ForwardRef IName -- not extern
 | Imported   ModuleIName Expr  -- Inlined
 | ImportLabel QName

 | NotInScope       HName
 | NotOpened        BitSet QName -- HName HName
 | AmbiguousBinding HName [(ModIName , IName)] -- same level binding overlap / overwrite

 | Importable ModuleIName IName -- Available externally but not obviously worth inlining
 | MixfixyVar Mixfixy           -- temp data fed to solvemixfixes

data Mixfixy = Mixfixy
 { ambigBind   :: Maybe QName -- mixfixword also bind, eg. `if_then_else_` and `then`
 , ambigMFWord :: [QMFWord]
 }

type ASMIdx = IName -- Field|Label→ Idx in sorted list (the actual index used at runtime)
data BiSub = BiSub { _pSub :: Type , _mSub :: Type }
-- Various casts inserted by inference
data BiCast
 = BiEQ
 | CastInstr PrimInstr
 | CastZext Int
 | CastProduct Int [(ASMIdx , BiCast)] -- number of drops, and indexes into parent struct
 | CastFields  [BiCast]

 | CastApp [BiCast] (Maybe [Type]) BiCast -- argcasts , maybe papcast , retcast
 | CastOver ASMIdx BiCast Expr Type

-- label for the different head constructors.
data Kind = KPrim PrimType | KArrow | KSum | KProd | KRec | KAny | KBound | KTuple | KArray
 deriving (Eq , Ord)

type ModuleBinds = V.Vector (LetMeta , Bind)
-- Each module has its own convention for numbering HNames - this must be resolved when importing binds
-- thus QName indicates which modules HName->IName convention to use (Also guarantees names are generative)
data JudgedModule = JudgedModule {
   modIName   :: IName
 , modHName   :: HName
 , jmINames   :: V.Vector HName
 , topINames  :: BitSet -- These allow QName -> TopBind vec lookup
 , labelINames:: BitSet
 , moduleTT   :: ModuleBinds
}

data SrcInfo = SrcInfo Text (VU.Vector Int)

-- Used by prettyCore functions and the error formatter
data BindSource = BindSource
  { srcINames :: ModIName -> IName -> Maybe HName
  , srcBindNames :: ModIName -> IName -> Maybe HName
  }

makeBaseFunctor ''Expr
makeBaseFunctor ''Term
makeBaseFunctor ''Type
makeLenses ''Type
makeLenses ''BiSub
