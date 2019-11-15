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

module CoreSyn
where

import Prim

import qualified Data.Vector        as V
import qualified Data.Text          as T
import qualified Data.IntMap.Strict as IM

type IName   = Int
type NameMap = V.Vector
type HName   = T.Text -- human readable name

type TypeMap      = NameMap Entity
type BindMap      = NameMap Binding
type DefaultDecls = IM.IntMap MonoType

-- note. algData is dataTypes     ++ aliases
--       bindings is constructors ++ binds
type ClassFns       = IM.IntMap Binding  -- indexed by polymorphic classFn's Iname
type ClassInsts     = IM.IntMap ClassFns
type ClassOverloads = IM.IntMap ClassInsts

type CoreModuleSig  = CoreModule -- difference is no lBinds are saved
data CoreModule     = CoreModule {
   algData   :: TypeMap -- data and aliases

 -- binds incl. constructors, locals, and class Fns (not overloads!)
 , bindings  :: BindMap
 , externs   :: TypeMap -- extern declarations

 -- typeclass resolution, indexed by the class polytype's iName
 , overloads :: ClassOverloads
 -- typeclass resolution when multiple Monotypes are possible
 , defaults  :: IM.IntMap MonoType -- eg. default Num Int

-- , tyFuns :: V.Vector TypeFunction
-- , copied :: Map IName Int -- track potentially copied data

 -- lookup table (for the interpreter)
 --, hNameBinds :: Data.Map HName IName
 --, hNameTypes :: Data.Map HName IName
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
-- vars coming into scope (via lambda, case expr, and expr+typesig)
 | LArg    { info :: Entity }
-- Term level GADT constructor (Type is known)
 | LCon    { info :: Entity }
 | LExtern { info :: Entity }
 | LClass  { info :: Entity } -- classFn declaration

-- an entity = info about | coreExpr | fn arg | decon arg
data Entity = Entity { -- entity info
   named    :: Maybe HName
 , typed    :: Type -- also terms (in a type context)
-- , source :: Maybe SourceEntity
 }

-- source info
--data SourceEntity = SourceEntity 
-- { src :: Maybe srcLoc
-- }

data CoreExpr
 = Var IName
 | Lit Literal
 | Instr PrimInstr
 | App CoreExpr [CoreExpr]
 | SwitchCase CoreExpr [(Literal, CoreExpr)]
 | DataCase CoreExpr
            [(IName, [IName], CoreExpr)] -- Con [args] -> expr
 | TypeExpr Type -- as return of `TypeFunction`
 | WildCard      -- TODO move to Literal

----------- Types -- ---------
-- note. alias vs name:
type UserType = Type -- user supplied type annotation
data Type
 = TyAlias IName   -- aliases (esp. to MonoTyData)

 | TyMono  MonoType -- monotypes 't'
 | TyPoly  PolyType -- constrained polytypes 'p', 's'
 | TyArrow [Type]  -- Kind 'function' incl. Sum/Product cons

 | TyExpr  TypeFunction -- incl. dependent types

 | TyUnknown -- needs to be inferred - the so-called box type.
 | TyBroken -- typecheck couldn't infer a coherent type

data MonoType
 = MonoTyPrim   PrimType
 | MonoRigid    IName    -- rigid typeVars subsume by comparing INames

data PolyType
 = PolyConstrain  [Type] -- (&) multiple typeclass constraints
 | PolyUnion      [Type] -- (|) union types (esp. type of typeclass)
 | PolyAny               -- Existential type (flexible typevars)
 -- Data is both a polytype (of it's alts) and a monotype
 | PolyData PolyType DataDef

-- Data saves bindMap names, since they're not in the typeMap
data DataDef = DataDef HName [(HName, [Type])]
-- | RecordDef HName [(HName, [(HName, Type)])]
-- | TupleDef [Type]

-- type functions: from trivial `data a = ..` to dependent types
data TypeFunction
 = TyDependent {
   tyArgs :: [IName]
 , tyExpr :: CoreExpr -- : CoreExpr.TypeExpr
 }
 | TyTrivialFn { -- trivial case: App (Con n) (TypeExp e)
   tyArgs :: [IName]
 , tyVal  :: Type
 }
 | TyApp Type [Type]

----------- Types -- --------- 
-- type vars are flexible = arbitrary types rather than variables.
-- boxy matching: fill boxes with monotypes
--   (no instantiation/skolemization)
--
-- By design, boxy matching is not an equivalence relation:
-- it is not reflexive (that would require guessing polytypes)
-- neither is it transitive |s|~s and s~|s| but not |s|~|s|.
-- similarly, boxy subsumption is neither reflexive nor transitive

deriving instance Show PolyType
deriving instance Show DataDef
deriving instance Show Binding
deriving instance Show MonoType
deriving instance Show Type
deriving instance Show TypeFunction
deriving instance Show CoreExpr
deriving instance Show Entity
deriving instance Show CoreModule

data TCError
 = UnifyFail { expected :: Entity, got :: Entity}
 deriving (Show)
