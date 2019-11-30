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

import qualified Data.Vector         as V
import qualified Data.Text           as T
import qualified Data.IntMap.Strict  as IM
import qualified Data.HashMap.Strict as HM

type IName   = Int
type NameMap = V.Vector
type HName   = T.Text -- human readable name

type TypeMap      = NameMap Entity
type BindMap      = NameMap Binding
type DefaultDecls = IM.IntMap MonoType

-- Classes
type ClassFns       = IM.IntMap Binding  -- indexed by polymorphic classFn's Iname
type ClassInsts     = IM.IntMap ClassFns
type ClassOverloads = IM.IntMap ClassInsts

data ImportList     = ImportList [CoreModule]
data CoreModule     = CoreModule {
   moduleName :: HName

 , algData    :: TypeMap -- data and aliases
 -- binds: constructors, locals, and class Fns (not overloads!)
 , bindings   :: BindMap

 , externs    :: TypeMap -- A subset of the bindMap

 -- typeclass  resolution, indexed by the class polytype's iName
 --  , classes  :: ? -- importers will want the classdecls
 , overloads  :: ClassOverloads
 -- default for otherwise ambiguous instances eg. default Num Int
 , defaults   :: IM.IntMap MonoType

-- , tyFuns :: V.Vector TypeFunction

 -- lookup tables (Used when module is imported and in the repl)
 , hNameBinds :: HM.HashMap HName IName
 , hNameTypes :: HM.HashMap HName IName
}

data Binding
 = LBind { -- let binding
   info  :: Entity  -- hname, type, source
 , args  :: [IName] -- the unique arg Names used locally by 'expr'
 , expr  :: CoreExpr
 }
 -- always inline this binding (esp. to access freevars)
 -- only used internally for pattern match deconstructions
 | Inline {
   info :: Entity
 , expr :: CoreExpr
 }
 | LArg    { info :: Entity } -- local vars via (lambda|case|expr:tysig)
 | LCon    { info :: Entity } -- Term level GADT constructor (Type is known)
 | LExtern { info :: Entity }
 | LClass  { info :: Entity } -- classFn declaration

-- an entity = info about anything we give an IName to.
data Entity = Entity { -- entity info
   named    :: Maybe HName
 , typed    :: Type
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
 | Case CoreExpr CaseAlts
 | TypeExpr Type -- as return of `TypeFunction`
 | WildCard

data CaseAlts
 = Switch [(Literal, CoreExpr)]
 | Decon  [(IName, [IName], CoreExpr)] -- Con [args] -> expr
 | Tuple  ([IName], CoreExpr)

----------- Types -- ---------
-- note. alias vs name:
type UserType = Type -- user supplied type annotation
data Type
 = TyAlias IName   -- aliases (esp. to MonoTyData)
 | TyMono  MonoType -- monotypes 't'
 | TyPoly  PolyType -- constrained polytypes 'p', 's'
 | TyArrow [Type]  -- Kind 'function' incl. Sum/Product cons
 | TyExpr  TypeFunction -- incl. dependent types

 | TyPAp [Type] [Type] -- for internal use
 | TyUnknown    -- needs to be inferred - the so-called box type.
 | TyBroken     -- typecheck couldn't infer a coherent type

data MonoType
 = MonoTyPrim   PrimType
 | MonoRigid    IName    -- rigid typeVars subsume by comparing INames

data PolyType
 = PolyConstrain  [Type] -- (&) multiple typeclass constraints
 | PolyUnion      [Type] -- (|) union types (esp. typeclass var)
 | PolyAny               -- Existential type (flexible typevars)
 -- Data is a polytype (of it's alts)
 | PolyData PolyType DataDef

-- Data saves bindMap names, since those otherwise can't be found in the typeMap
data DataDef
 = DataDef   HName [(HName, [Type])]
 | RecordDef HName [(HName, [FieldDecl])]
 | ModuleDef HName CoreModule
data FieldDecl = FieldDecl HName Type

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

deriving instance Show PolyType
deriving instance Show DataDef
deriving instance Show FieldDecl
deriving instance Show Binding
deriving instance Show MonoType
deriving instance Show Type
deriving instance Show TypeFunction
deriving instance Show CoreExpr
deriving instance Show CaseAlts
deriving instance Show Entity
deriving instance Show CoreModule

data TCError
 = UnifyFail { expected :: Entity, got :: Entity}
 deriving (Show)
