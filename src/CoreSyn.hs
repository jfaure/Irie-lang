-- Core Language
-- recall: ParseSyn >> CoreExpr >> STG codegen
-- The language for type judgements: checking and inferring
--
-- ParseSyn vs Core
-- > no local variables
-- > all vars have a unique name
-- > no free variables (explicit function arguments)
-- > all entities are annotated with a type (can be TyUnknown)
-- - ultimately stg must have only monotypes
--
-- despite dependent types, core seperates terms and types
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
import qualified Data.List as DL -- intersperse

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
-- let bindings assigned to a coreExpr
 = LBind {
   args  :: [Name] -- the unique arg Names used by 'expr'
 , expr  :: CoreExpr
 , info  :: Entity -- !
 }
-- vars coming into scope (via lambda or case expr)
 | LArg { info :: Entity }
-- Term level GADT constructor (Type is known)
 | LCon { info :: Entity }

-- ? does type judging ever create new bindings ?
-- algData should perhaps not exist (merge into bindings)
data CoreModule = CoreModule {
   algData  :: TypeMap -- named types (data, aliases)
 , bindings :: ExprMap -- incl. constructors and locals
 , defaults :: Map PolyType MonoType -- eg. default Num Int
 --, hNameMap :: Data.Map HName IName -- lookup table
 -- may be useful in the interpreter
 }

-- an entity = info about an expression
data Entity = Entity -- entity info
 { named    :: Maybe HName
 , typed    :: Type -- also terms (in a type context)
 , universe :: Int -- term/type/kind/sort/...
-- , source :: Maybe SourceEntity
 }

-- source info
-- how much info do we care about ?
-- like depth inside bindings, freevars etc..
--data SourceEntity = SourceEntity 
-- { src :: Maybe srcLoc
-- }

uniTerm : uniType : uniKind : uniSort : _ = [0..] :: [Int]

data CoreExpr
 = Var Name
 | Lit Literal
 | Instr PrimInstr [CoreExpr]
 | App CoreExpr [CoreExpr]
 | Let [Binding] CoreExpr -- there are no bindings in core..?
 | SwitchCase CoreExpr [(Literal, CoreExpr)]
 | DataCase CoreExpr
            [(IName, [IName], CoreExpr)] -- Con [args] -> expr
 | TypeExpr Type -- dependent types
 | WildCard

-- Prim: types (and signatures) are richer than llvm primitives
-- so we delay the conversion to STG
-- TODO where are the type signatures ?
-- TODO special constructors for primitive types ? tuple/array..
data PrimInstr = Add  | Sub  | Mul  | Div
               | Fadd | FSub | FMul | FDiv

data Literal
 = ExternFn LLVM.AST.Operand -- can use LLVM..typeOf on it
 | LlvmLit  LLVM.AST.Operand -- anything else

----------- Types -- ---------
type UserType = Type -- user supplied type annotation
data Type
 = TyVar IName

 | TyMono MonoType -- monotypes 't'
 | TyPoly PolyType -- constrained polytypes 'p', 's'
 | TyArrow [Type]  -- Kind 'function' incl. Sum/Product cons

 | TyExpr CoreExpr -- dependent type

 | TyUnknown -- needs to be inferred - the so-called boxy type.
 | TyBroken -- typecheck couldn't infer a coherent type

-- Note. data is up to stg, Core only needs GADT type sigs
data MonoType
 = MonoTyLlvm LLVM.AST.Type
 | MonoTyData IName
 | MonoTyClass -- ?!

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

deriving instance Show PrimInstr
deriving instance Show Forall
deriving instance Show Binding
deriving instance Show MonoType
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

ppType :: Type -> String = \case
 TyVar nm -> "$" ++ show nm
 TyMono m -> case m of
   MonoTyLlvm lty -> case lty of
     LLVM.AST.IntegerType n -> "int" ++ show n
     other -> show other
   MonoTyData nm -> "data." ++ show nm

 TyPoly p -> show p
 TyArrow tys -> "(" ++ (concat $ DL.intersperse " -> " 
                                (ppType <$> tys)) ++ ")"
 TyExpr coreExpr -> _
 TyUnknown -> "TyUnknown"
 TyBroken  -> "tyBroken"

ppCoreExpr :: (IName -> String) -> CoreExpr -> String = \deref -> let ppCoreExpr' = ppCoreExpr deref in \case
 Var n -> {- show n ++-} deref n
 Lit l -> show l
 App f args -> ppCoreExpr' f ++" "++ concat (DL.intersperse " " ((\x -> "(" ++ ppCoreExpr' x ++ ")" ) <$> args))
 Let binds e -> _ --"let "++ppBinds (\x->Nothing) binds++"in "++ ppCoreExpr e
 SwitchCase c alts -> "case " ++ ppCoreExpr' c ++ show alts
 DataCase c alts -> "case " ++ ppCoreExpr' c ++ " of" ++ "\n" ++ (concat $ DL.intersperse "\n" $ (ppDataAlt deref)<$> alts)
 TypeExpr ty -> show ty
 l -> show l

ppDataAlt :: (IName -> String) -> (IName, [IName], CoreExpr) -> String
ppDataAlt deref (con, args, ret) = 
 deref con ++
 (concatMap (\x -> " " ++ (deref x)) args) ++ " -> " ++ 
 ppCoreExpr deref ret

ppBinds :: [Binding] -> (IName -> String) -> String
 = \l f -> concatMap (ppBind f "\n   ") l
ppBind f indent b = indent ++ case b of
  LBind args e entity -> "(" ++ case named entity of
     { Just nm -> show nm ; Nothing -> "\\" }
    ++ " " ++ show args 
    ++ " : " ++ ppType (typed entity) ++ ")"
    ++ indent ++ "  = " ++ ppCoreExpr f e
  LArg a -> "larg: " ++ ppEntity a
  LCon a -> "lcon: " ++ ppEntity a

ppCoreModule :: CoreModule -> String
 = \(CoreModule typeMap bindings defaults)
  -> let f i = case named $ info $ (bindings V.! i) of
           Just x -> T.unpack x
           Nothing-> "_"
     in "bindings: " ++ concat ((ppBind f "\n  ") <$> bindings)
      ++ "\n\n" ++ "types: " ++ show typeMap
      ++ "\n\n" ++ "defaults: " ++ show defaults

ppEntity (Entity nm ty uni) = 
  case nm of
    Just nm -> show nm
    Nothing -> "\\_"
  ++ " : " ++ ppType ty ++ " (" ++ show uni ++ ")"
