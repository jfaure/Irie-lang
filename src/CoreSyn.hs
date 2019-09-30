-- Core Language
-- recall: ParseSyn >> CoreExpr >> STG codegen
-- The language for type judgements: checking and inferring
--
-- !! Important points about Core:
-- No local variables: all vars have a unique name (Int)
-- No free variables. only explicit funcion arguments
-- No lambdas/anonymous type annotations: Let-bind them.
-- source/origin annotations (for error msgs)

{-# LANGUAGE StandaloneDeriving, DeriveFunctor, GeneralisedNewtypeDeriving, LambdaCase, ScopedTypeVariables #-}
module CoreSyn where

import qualified LLVM.AST.Type
import qualified LLVM.AST -- (Operand, Type, Instruction)
import qualified LLVM.AST.Typed (typeOf)
import qualified LLVM.AST.Constant as LC
import Data.Map.Strict
import Control.Monad.State.Strict
import Control.Applicative

import qualified Data.Vector as V
import qualified Data.Text as T

type Name    = Int -- deprec

type IName   = Int
type NameMap = V.Vector
type HName   = T.Text -- human readable name

type TypeMap = NameMap Entity
type ExprMap = NameMap Binding
type BindMap = NameMap Binding

-- Binding: save argNames brought into scope
-- since all vars get a unique name, we need this for locals,
-- note. top binds/data are always in scope, so no need.
data Binding
-- Normal let binding (with info)
 = LBind {
   args  :: [Name] -- the unique Names for this function
 , expr  :: CoreExpr
 , info  :: Entity -- !
 }
-- Function arg (no expr, but we need to judge it's type)
 | LArg { info :: Entity }
-- Term level GADT constructor (Type is a TyArrow)
 | LCon { conTypes :: Type }

data CoreModule = CoreModule {
   types         :: TypeMap -- all named types (incl data)
 , topExprs      :: ExprMap -- top level binds incl constructors
 , localBindings :: ExprMap -- all other variables in module
 , defaults      :: Map PolyType MonoType -- eg. default Num Int
 }

-- an entity = info about an expression
data Entity = Entity -- entity info
 { named    :: Maybe HName
 , typed    :: Type -- also terms (in a type context)
 , universe :: Int -- term/type/kind/sort/...
-- , userSource :: Maybe SourceEntity
 }
-- info about something introduced by user
--data SourceEntity = SourceEntity {
--   origin :: UserOrigin
-- , src :: Maybe srcLoc
--}
--data UserOrigin = FreeVar | LocalArg | Global

-- type check environment
data TCEnvState = TCEnvState {
   coreModule :: CoreModule
 , errors :: [TCError]
}
type TCEnv a = State TCEnvState a

uniTerm : uniType : uniKind : uniSort : _ = [0..] :: [Int]

data CoreExpr
 = Var Name
 | Lit Literal
 | Instr Primitive
 | App CoreExpr [CoreExpr]
 | Let [Binding] CoreExpr
 | SwitchCase CoreExpr [(Literal, CoreExpr)]
 | DataCase CoreExpr
            [(Name, [Name], CoreExpr)] -- Con [args] -> expr
 | TypeExpr Type -- dependent types
 | WildCard

-- Prim: cannot use llvm Instructions because of typing issues
-- eg. (+) : Num a => a->a->a (or even more complicated)
-- vs FAdd,Add that take LLVM.AST.Operands (and flags).
data Primitive
 = Add | Sub | Mul | Div
 deriving Show

data Literal
 = ExternFn LLVM.AST.Operand -- can use LLVM..typeOf on it
 | LlvmLit  LLVM.AST.Operand -- anything else

----------- Types -- ---------
type UserType = Type -- user supplied type annotation
data Type
 = TyVar HName

 | TyMono MonoType -- monotypes 't'
 | TyPoly PolyType -- constrained polytypes 'p', 's'
 | TyArrow [Type] Type -- Kind 'function' incl. Sum/Product cons

 | TyExpr CoreExpr -- dependent type

 | TyUnknown -- needs to be inferred - the so-called boxy type.
 | TyBroken -- typecheck error: skip and continue

-- data is up to stg, Core only knows GADT style Con types
data MonoType
 = MonoTyLlvm LLVM.AST.Type
 | MonoTyData Name SumData
data SumData     = SumData [ProductData]
data ProductData = ProductData Name [Type]

type PolyType = Forall
data Forall
 = ForallAnd [Type] -- & constraints
 | ForallOr  [Type] -- | constraints
 | ForallAny        -- Void =~ an opaque monotype

----------- Types -- --------- subsumption: s1 <= s2 means s1 is at
--least as polymorphic as s2 (it's less specific) sharing: forall a
--b. a->[b] <= forall a. a->[a] note: forall a. Int->a <=
--Int->(forall b. b->b) (higher rank polytypes are less polymorphic)
--
-- Judgements combine inference and checking: box: an inferred
-- vanilla type (boxes cannot be nested: outside is checked, inside
-- inferred) boxy types: contain >=0 boxes boxy matching: fill boxes
-- with monotypes (no instantiation/skolemization) pushBox: if entire
-- result type is a box, push down the fn App and try again =~ make
-- new holes for arg and ret types
--
-- we need that |forall b. b->b| <= forall b. b->b box meets box
-- implies: a->|s| ~ |a->s| , since otherwise |s|~|s| which is wrong
-- By design, boxy matching is not an equivalence relation: it is not
-- reflexive (that would require guessing polytype info) neither is
-- it transitive |s|~s and s~|s| but not |s|~|s|.  likewise
-- subsumption is neither reflexive nor transitive (for boxy types)
--
-- Removing boxes: if s->s <= |s|->s, then we should derive
-- s->s<=s->s we can 'push boxes down': if |s->s| <= s->s, we also
-- have |s|->|s| <= s->s this can be proven to preserve boxy
-- matching, subsumption and typability Unboxing lemmas: (s1|>s2
-- means that s2 can be constructed from s1 by removing or pushing
-- boxes down the AST) 1. if s1~s2 and s1|>s3 and s2|>s4 then s3~s4
-- 2. if s1<=s2 and s1|>s3 and s2|>s4 then s3<=s4 3. if t:p1 and
-- p1|>p2 then t:p2 note. for monotypes, boxing/unboxing does not
-- matter
--
-- type vars are flexible = arbitrary types rather than variables.

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
instance Show Literal where
  show (LlvmLit (LLVM.AST.ConstantOperand (LC.Int bits val))) =
    "(i"++show bits++show val++")"
  show (LlvmLit f) = show f
  show (ExternFn f) = show f
deriving instance Show CoreExpr
deriving instance Show Entity
deriving instance Show CoreModule

typeOfLiteral :: Literal -> Type
typeOfLiteral l =
  let go = TyMono . MonoTyLlvm . LLVM.AST.Typed.typeOf
  in case l of
  ExternFn f -> go f
  LlvmLit l -> go l

data TCError
 = UnifyFail { expected :: Entity, got :: Entity}
 deriving (Show)

ppCoreExpr :: CoreExpr -> String = \case
 Var n -> "var" ++ show n
 Lit l -> show l
 App f args -> ppCoreExpr f ++" $ "++ show (ppCoreExpr <$> args)
 Let binds e -> "let "++ppBinds binds++"in "++ ppCoreExpr e
 SwitchCase c alts -> "case " ++ ppCoreExpr c ++ show alts
 TypeExpr ty -> show ty
 l -> show l

ppBinds :: [Binding] -> String = concatMap (ppBind "   ")
ppBind indent = \case
  LBind args e entity -> "\\" ++ show args 
    ++ "(" ++ show entity ++ ") -> " ++ ppCoreExpr e ++ "\n"
  LArg a -> show a

ppCoreModule :: CoreModule -> String
 = \(CoreModule typeMap topExprs localBindings defaults)
  -> "top Binds: " ++ concatMap (ppBind "  ") topExprs
      ++ "\n\n" ++ "local Binds: " ++ concatMap (ppBind "  ") localBindings
      ++ "\n\n" ++ "types: " ++ show typeMap
      ++ "\n\n" ++ "defaults: " ++ show defaults
