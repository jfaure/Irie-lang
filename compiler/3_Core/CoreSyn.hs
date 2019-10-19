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

module CoreSyn where

import qualified LLVM.AST.Type
import qualified LLVM.AST -- (Operand, Type, Instruction)
import qualified LLVM.AST.Typed (typeOf)
import LLVM.AST.Constant as LC
import Data.Map.Strict
import Control.Monad.State.Strict
import Control.Applicative

import qualified Data.Vector as V
import qualified Data.Text as T
import qualified Data.List as DL -- intersperse

type IName   = Int
type NameMap = V.Vector
type HName   = T.Text -- human readable name

type TypeMap = NameMap Entity
type ExprMap = NameMap Binding
type BindMap = NameMap Binding

-- TODO OCaml style modules
data CoreModule = CoreModule {
   algData  :: TypeMap -- named types (data, aliases)
 , bindings :: ExprMap -- incl. constructors and locals
 , defaults :: Map PolyType MonoType -- eg. default Num Int
 , tyFuns   :: V.Vector TypeFunction
 --, hNameMap :: Data.Map HName IName -- lookup table (for the interpreter)
 }

-- Binding: save argNames brought into scope
-- since all vars get a unique name, we need this for locals,
-- note. top binds/data are always in scope, so no need.
data Binding
-- let bindings assigned to a coreExpr
 = LBind {
   args  :: [IName] -- the unique arg Names used by 'expr'
 , expr  :: CoreExpr
 , info  :: Entity  -- hname, type, source
 }
-- vars coming into scope (via lambda or case expr)
 | LArg { info :: Entity }
-- Term level GADT constructor (Type is known)
 | LCon { info :: Entity }

-- an entity = info about | coreExpr | fn arg | decon arg
data Entity = Entity { -- entity info
   named    :: Maybe HName
 , typed    :: Type -- also terms (in a type context)
 , universe :: Int -- term/type/kind/sort/...
-- , source :: Maybe SourceEntity
 }

-- source info
--data SourceEntity = SourceEntity 
-- { src :: Maybe srcLoc
-- }

uniTerm : uniType : uniKind : uniSort : _ = [0..] :: [Int]

data CoreExpr
 = Var IName
 | Lit Literal
 | Instr PrimInstr [CoreExpr]
 | App CoreExpr [CoreExpr]
 | SwitchCase CoreExpr [(Literal, CoreExpr)]
 | DataCase CoreExpr
            [(IName, [IName], CoreExpr)] -- Con [args] -> expr
 | TypeExpr Type -- can only appear inside `TypeFunction`
 | WildCard

-- Prim: types (and signatures) are richer than llvm primitives
-- so we delay the conversion to STG
-- TODO where are the type signatures - Prim module perhaps ?
-- TODO special constructors for primitive types ? tuple/array..
data PrimInstr = Add|Sub|Mul|Div|Fadd|FSub|FMul|FDiv

data Literal
 = ExternFn LLVM.AST.Operand  -- can use LLVM..typeOf on it
 | LlvmLit  LC.Constant -- anything else

----------- Types -- ---------
type UserType = Type -- user supplied type annotation
data Type
 = TyAlias IName   -- aliases (esp. to MonoTyData)

 | TyMono MonoType -- monotypes 't'
 | TyPoly PolyType -- constrained polytypes 'p', 's'
 | TyArrow [Type]  -- Kind 'function' incl. Sum/Product cons

 | TyExpr TypeFunction -- incl. dependent types

 | TyUnknown -- needs to be inferred - the so-called boxy type.
 | TyBroken -- typecheck couldn't infer a coherent type

-- Note. data is up to stg, Core only handles GADT-style sigs
-- TODO subtypes, (.) accessor
-- note we store the hname directly in the MonoTyData
data MonoType
 = MonoTyLlvm LLVM.AST.Type
 | MonoTyData HName [(HName, Type)] -- self-name and Gadt constructors
 | MonoTyClass -- ?!

type PolyType = Forall
data Forall -- typeclass & and | operations
 = ForallAnd [Type] -- (&) multiple typeclass constraints
 | ForallOr  [Type] -- (|) union types (esp. type of typeclass)
 | ForallAny        -- Existential type (since typevars are flexible)

-- type functions: from trivial `data a = ..` to dependent types
-- TODO kind functions, type matching, type classes, subtypes
data TypeFunction = TypeFunction {
   tyArgs :: [IName]
 , tyExpr :: CoreExpr -- obviously must return a `TypeExpr`
 }

----------- Types -- --------- 
-- type vars are flexible = arbitrary types rather than variables.
-- boxy matching: fill boxes with monotypes
--   (no instantiation/skolemization)
--
-- By design, boxy matching is not an equivalence relation:
-- it is not reflexive (that would require guessing polytypes)
-- neither is it transitive |s|~s and s~|s| but not |s|~|s|.
-- similarly, boxy subsumption is neither reflexive nor transitive

deriving instance Show PrimInstr
deriving instance Show Forall
deriving instance Show Binding
deriving instance Show MonoType
deriving instance Show Type
deriving instance Show TypeFunction
instance Show Literal where
  show (LlvmLit (LC.Int bits val)) =
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
  LlvmLit l -> go (LLVM.AST.ConstantOperand l)

data TCError
 = UnifyFail { expected :: Entity, got :: Entity}
 deriving (Show)

ppType :: Type -> String = \case
 TyAlias nm -> "$" ++ show nm
 TyMono m -> case m of
   MonoTyLlvm lty -> case lty of
     LLVM.AST.IntegerType n -> "int" ++ show n
     other -> show other
   MonoTyData nm cons -> "data.$" ++ show nm

 TyPoly p -> show p
 TyArrow tys -> "(" ++ (concat $ DL.intersperse " -> " 
                                (ppType <$> tys)) ++ ")"
 TyExpr coreExpr -> error "tyexpr"
 TyUnknown -> "TyUnknown"
 TyBroken  -> "tyBroken"

ppCoreExpr :: (IName -> String) -> String -> CoreExpr -> String
 = \deref indent ->
 let ppCoreExpr' = ppCoreExpr deref indent
 in \e -> case e of
  Var n -> {- show n ++-} deref n
  Lit l -> show l
  App f args -> ppCoreExpr' f ++" "++ concat (DL.intersperse " " ((\x -> "(" ++ ppCoreExpr' x ++ ")" ) <$> args))
  -- Let binds e -> error "let in coreexpr" --"let "++ppBinds (\x->Nothing) binds++"in "++ ppCoreExpr e
  SwitchCase c alts -> "case " ++ ppCoreExpr' c ++ show alts
  DataCase c alts -> "case " ++ ppCoreExpr' c ++ " of" ++ "\n" ++ (concat $ DL.intersperse "\n" $ (ppDataAlt deref (indent++"  "))<$> alts)
  TypeExpr ty -> show ty
  l -> show l

ppDataAlt :: (IName -> String) -> String -> (IName, [IName], CoreExpr) -> String
ppDataAlt deref indent (con, args, ret) = indent ++
 deref con ++ (concatMap (\x -> " " ++ (deref x)) args) ++ " -> " ++ 
 ppCoreExpr deref (indent++"  ") ret

ppBinds :: [Binding] -> (IName -> String) -> String
 = \l f -> concatMap (ppBind f "\n   ") l
ppBind f indent b = indent ++ case b of
  LBind args e entity -> case named entity of
     { Just nm -> show nm ; Nothing -> "\\" }
    ++ " " ++ show args 
    ++ " : " ++ ppType (typed entity)
    ++ indent ++ "  = " ++ ppCoreExpr f "" e
  LArg a -> "larg: " ++ ppEntity a
  LCon a -> "lcon: " ++ ppEntity a

ppCoreModule :: CoreModule -> String
 = \(CoreModule typeMap bindings defaults tyFuns)
  -> "bindings: " ++ concat ((ppBind (bind2HName bindings) "\n") <$> bindings)
      ++ "\n\n" ++ "types: " ++ (concatMap (\x->ppEntity x ++ "\n") typeMap)
      ++ "\n\n" ++ "defaults: " ++ show defaults
      ++ "\n\n" ++ "TyFuns: " ++ show tyFuns 

-- function to convert a  binding to a stringname
bind2HName bindings i = case named $ info $ (bindings V.! i) of
       Just x -> T.unpack x
       Nothing-> "_"

ppCoreBinds :: CoreModule -> String
 = \cm
   -> let binds = bindings cm
          top = V.filter (\case { LBind{} -> True ; _ -> False }) binds
      in concat ((ppBind (bind2HName binds) "\n") <$> top)

ppEntity (Entity nm ty uni) = 
  case nm of
    Just nm -> show nm
    Nothing -> "\\_"
  ++ " : " ++ ppType ty -- ++ " (" ++ show uni ++ ")"
