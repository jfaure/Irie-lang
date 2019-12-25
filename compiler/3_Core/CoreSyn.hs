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
import qualified Data.Map.Strict as M

type IName   = Int    -- Int name: index into bind|type vectors
type IName0  = IName  -- IName of a type
type HName   = T.Text -- human readable name

type TypeMap = V.Vector Entity
type BindMap = V.Vector Binding

data ImportList     = ImportList [CoreModule]
data CoreModule     = CoreModule {
   moduleName :: HName

 , algData    :: TypeMap -- data and aliases
 -- binds: constructors, locals, and class Fns (+ overloads!)
 , bindings   :: BindMap

 , classDecls :: V.Vector ClassDecl -- so importers can check instances
 , defaults   :: IM.IntMap MonoType
 , fixities   :: HM.HashMap HName Fixity

 -- specialized alg data instances (created by typejudge)
 -- TyDynInstances contains indexes into this
 , tyConInstances :: V.Vector Entity

 -- lookup tables (Used when module is imported and in the repl)
 , hNameBinds :: HM.HashMap HName IName
 , hNameTypes :: HM.HashMap HName IName
}

-------------
-- classes --
-------------
-- classdecl: used to check instances / make overloads
data ClassDecl = ClassDecl {
   className :: HName
 , classFns  :: V.Vector ClassFn
}
data ClassFn = ClassFn {
   classFnInfo :: Entity      -- the tyFunction TODO use TyFunction
 , defaultFn   :: Maybe IName --Overload
}
type ClassDefaults  = IM.IntMap MonoType

data Binding
 = LBind { -- let binding
   info  :: Entity  -- hname, type, source
 , args  :: [IName] -- the unique arg Names used locally by 'expr'
 , expr  :: CoreExpr
 }
 -- always inline this binding (esp. to access freevars)
 -- only used internally for pattern match deconstructions
 | Inline { info :: Entity , expr :: CoreExpr }
 | LLit   { info :: Entity , lit  :: Literal }
 | LArg   { info :: Entity } --local vars via (lambda|case|expr:tysig)
 | LCon   { info :: Entity } --Term level GADT constructor(Type is known)
 | LExtern{ info :: Entity }
 | LClass {
   info        :: Entity -- TypeFunction
 , classNm     :: HName  -- change to IName ?
 , overloads   :: M.Map Type IName -- instanceIds
 }
 -- typevar is accessed in the function signature
 | LTypeVar { info :: Entity }
-- | LBuiltinSizeof

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
 = Var      IName
-- | ExtVar   IName IName -- lookup in other module
 | Lit      Literal
 | Instr    PrimInstr
 | App      CoreExpr [CoreExpr]
 | Case     CoreExpr CaseAlts
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
 = TyAlias IName    -- aliases (esp. to MonoTyData)
 | TyRigid IName    -- correspond to arguments of type constructors
 | TyMono  MonoType -- monotypes 't'
 | TyPoly  PolyType -- constrained polytypes 'p', 's'
 | TyArrow [Type]   -- Kind 'function' incl. Sum/Product cons

 | TyExpr  TypeFunction -- [IName] Type
 | TyDep   CoreExpr
 | TyCon   Type [Type]  -- make a new type from a TyFun
 | TyTy

 | TyUnknown    -- needs to be inferred - the so-called box type.
 -- markers for internal use
 | TyInstance IName Type -- name of overload and return type
 | TyDynInstance { --binding doesn't exist before tyjudge
   -- because it's a specialized data constructor
   dataIdx :: IName
 , conIdx  :: IName
 , ty      :: Type
 }

 | TyPAp [Type] [Type]   -- for internal use
 | TyBroken              -- typejudge couldn't infer a coherent type

-- type functions: eg `data a = ..`
data TypeFunction
 = TyTrivialFn { -- trivial case: App (Con n) (TypeExp e)
   tyArgs :: [IName0]
 , tyVal  :: Type
 }

data MonoType
 = MonoTyPrim   PrimType
 | MonoSubTy {
   rigidSubNm :: IName
 , parentTy   :: IName -- case expressions need the parent type info
 , conIndx    :: Int   -- indx of constructor in the data
 }

data PolyType
 = PolyConstrain  [Type] -- (&) multiple typeclass constraints
 | PolyUnion      [Type] -- (|) union types (esp. typeclass var)
 | PolyAny               -- some fns merely pass on polymorhism (void*)
 -- Data is a polytype (of it's alts)
 | PolyData PolyType DataDef

-- Data saves HNames, so they are reachable from the typeMap
data DataDef
 = DataDef    HName [(HName, [Type])]
-- | RecordDef HName [(HName, [FieldDecl])] -- FieldDecl HName Type
-- | NewTypeDef [IName] DataDef
 | ModuleDef  HName CoreModule
-- data NewType = NewType { parentData :: DataDef , newType :: DataDef }

data Fixity = Fixity Int Assoc
data Assoc = LAssoc | RAssoc deriving (Eq, Show)

deriving instance Show PolyType
deriving instance Show DataDef
deriving instance Show ClassDecl
deriving instance Show ClassFn
deriving instance Show Binding
deriving instance Show MonoType
deriving instance Show Type
deriving instance Show TypeFunction
deriving instance Show CoreExpr
deriving instance Show CaseAlts
deriving instance Show Entity
deriving instance Show CoreModule
deriving instance Show Fixity

deriving instance Ord PolyType
deriving instance Ord DataDef
deriving instance Ord ClassDecl
deriving instance Ord ClassFn
deriving instance Ord Binding
deriving instance Ord MonoType
deriving instance Ord Type
deriving instance Ord TypeFunction
deriving instance Ord CoreExpr
deriving instance Ord CaseAlts
deriving instance Ord Entity
deriving instance Ord CoreModule
deriving instance Ord Fixity
deriving instance Ord Assoc

deriving instance Eq PolyType
deriving instance Eq DataDef
deriving instance Eq ClassDecl
deriving instance Eq ClassFn
deriving instance Eq Binding
deriving instance Eq MonoType
deriving instance Eq Type
deriving instance Eq TypeFunction
deriving instance Eq CoreExpr
deriving instance Eq CaseAlts
deriving instance Eq Entity
deriving instance Eq CoreModule
deriving instance Eq Fixity

data TCError
 = UnifyFail { expected :: Entity, got :: Entity}
 deriving (Show)
