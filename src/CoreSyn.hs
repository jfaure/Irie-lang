-- Core Language
-- recall: ParseSyn >> CoreExpr >> STG codegen
-- The language for type judgements: checking and inferring
--
-- !! Important points about Core:
-- No free variables. they're moved to explicit funcion arguments
-- No lambdas or anonymous type annotations: they're given a unique name and let bound
-- Maintain source/origin annotations for producing error messages

-- Type checking in the presence of higher rank / dependent types can be undecidable !

{-# LANGUAGE StandaloneDeriving #-}
module CoreSyn where

import qualified LLVM.AST.Type
import qualified LLVM.AST (Operand, Type)
import Data.Vector
import Data.Map.Strict
import qualified Data.Text as T

type Name    = Int
type NameMap = Vector
type HName   = T.Text -- human readable name

type TypeMap = NameMap Entity
type ExprMap = NameMap Binding

-- Binding: save the number of args brought into scope
data Binding = Binding {
   arity :: Int
 , expr  :: CoreExpr
 , info  :: Entity
}

data CoreModule = CoreModule {
   types    :: TypeMap -- all named types (incl types of data)
 , topExprs :: ExprMap -- top level incl constructors
 , defaults :: Map PolyType MonoType -- eg. default Num Int
 }

-- an entity = info about an expression
data Entity = Entity -- entity info
 { named    :: Maybe HName
 , typed    :: Type
 , universe :: Int -- term/type/kind/sort/...
-- , userSource :: Maybe SourceEntity
 }
-- info about something introduced by user
data SourceEntity = SourceEntity {
 , origin :: UserOrigin
 , src :: Maybe srcLoc
}
data UserOrigin = FreeVar | LocalArg | Global

-- type check environment
data TCEnvState = TCEnvState {
   mod :: CoreModule
 , localBindings :: [V.Vector Entity]
}
newtype TCEnv a = TCEnv { unTCEnv :: State TCEnvState a }
  deriving
 (Functor, Alternative, Applicative, Monad, MonadState
 , MonadPlus)

uniTerm : uniType : uniKind : uniSort : _ = [0..] :: [Int]

data CoreExpr
 = Var Name
 | Lit Literal
 | App CoreExpr [CoreExpr]
 | Let [Binding] CoreExpr
 | Case CoreExpr [(Pat, CoreExpr)]
 | TypeExpr Type -- dependent types

-- patterns: anything that can be matched against
data Pat = PVar Name | PLit Literal
 | PApp Name [Pat] | PWildCard | PTuple [Pat]

data Literal
 = ExternFn LLVM.AST.Operand -- can use LLVM..typeOf on it
 | LlvmLit  LLVM.AST.Operand -- anything else
 | Con -- constructors are considered literals because they're opaque

-----------
-- Types --
-----------
type UserType = Type -- user supplied type annotation
data Type
 = TyRef Name

 | TyMono MonoType -- monotypes 't'
 | TyPoly PolyType -- constrained polytypes 'p', 's'

 -- types with kind 'function', incl. Sum/Product constructors
 | TyArrow [Type] Type 

 | TyExpr CoreExpr -- dependent type

 -- a request that this type be inferred
 | TyUnknown

 -- type check failed on this type: it can't be trusted,
 -- but we can skip it and check the rest of the program
 | TyBroken

-- algebraic data is up to stg
-- Core only needs the GADT style types of constructors
data MonoType
 = MonoTyLlvm LLVM.AST.Type
 | MonoTyData SumData
data SumData     = SumData          [ProductData]
data ProductData = ProductData Name [Type]

type PolyType = Forall
data Forall
 = ForallAnd [Type] -- & constraints
 | ForallOr  [Type] -- | constraints
 | ForallAny        -- Void =~ an opaque monotype

deriving instance EQ SumData
deriving instance EQ ProductData
deriving instance EQ MonoType
-----------
-- Types --
-----------
-- subsumption: s1 <= s2 means s1 is at least as polymorphic as s2
--   (it's less specific)
-- sharing: forall a b. a->[b] <= forall a. a->[a]
-- note: forall a. Int->a <= Int->(forall b. b->b)
--   (higher rank polytypes are less polymorphic)
--
-- Judgements combine inference and checking:
-- box: an inferred vanilla type
--  (boxes cannot be nested: outside is checked, inside inferred)
-- boxy types: contain >=0 boxes
-- boxy matching: fill boxes with monotypes (no instantiation/skolemization)
-- pushBox: if entire result type is a box, push down the fn App and try again
-- =~ make new holes for arg and ret types
--
-- we need that |forall b. b->b| <= forall b. b->b
-- box meets box implies: a->|s| ~ |a->s| , since otherwise |s|~|s| which is wrong
-- By design, boxy matching is not an equivalence relation: it is not reflexive
-- (that would require guessing polytype info)
-- neither is it transitive |s|~s and s~|s| but not |s|~|s|.
-- likewise subsumption is neither reflexive nor transitive (for boxy types)
--
-- Removing boxes:
-- if s->s <= |s|->s, then we should derive s->s<=s->s
-- we can 'push boxes down': if |s->s| <= s->s, we also have |s|->|s| <= s->s
--   this can be proven to preserve boxy matching, subsumption and typability
-- Unboxing lemmas: (s1|>s2 means that s2 can be constructed from s1
--   by removing or pushing boxes down the AST)
-- 1. if s1~s2 and s1|>s3 and s2|>s4 then s3~s4
-- 2. if s1<=s2 and s1|>s3 and s2|>s4 then s3<=s4
-- 3. if t:p1 and p1|>p2 then t:p2
-- note. for monotypes, boxing/unboxing does not matter
--
-- Environment: types support lexically scoped type variables
-- scoped type vars are flexible = arbitrary types rather than variables.

-- types are stratified into monotypes 't' and polytpes 's' and 'p'
-- 'p' types have no toplevel foralls, but may contain polytypes
-- Boxed (inferred) types are stratified in exactly the same way
-- Note: boxes are not nested, so we track it during type judging

deriving instance Show Forall
deriving instance Show Binding
deriving instance Show MonoType
deriving instance Show SumData
deriving instance Show ProductData
deriving instance Show Type
deriving instance Show Pat
deriving instance Show Literal
deriving instance Show CoreExpr
deriving instance Show Entity
deriving instance Show CoreModule
