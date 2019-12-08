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

type IName   = Int    -- Int name: index into bind|type vectors
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
data Overload = Overload {
   classFnId  :: IName
 , instanceId :: IName
 , instanceTy :: Type
}
-- classdecl: used to check instances / make overloads
data ClassDecl = ClassDecl {
   className :: HName
 , classVars :: V.Vector HName
 , classFns  :: V.Vector ClassFn
}
data ClassFn = ClassFn {
-- class decls bring some polytypes into scope for their overloads
-- TODO move to tyfunction
   argIndxs    :: [Int] -- the rigid typevars in the function signature
 , classFnInfo :: Entity  -- fnsig is almost always tyArrow
 , defaultFn   :: Maybe Overload
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
-- | LClass { info :: Entity }
 | LClass {
   info :: Entity
 , overloads :: V.Vector Overload -- [Binding]
 }

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
 = TyAlias IName   -- aliases (esp. to MonoTyData)
 | TyMono  MonoType -- monotypes 't'
 | TyPoly  PolyType -- constrained polytypes 'p', 's'
 | TyArrow [Type]  -- Kind 'function' incl. Sum/Product cons
-- | TyCon   TypeFunction
 | TyExpr  TypeFunction -- incl. dependent types
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

data MonoType
 = MonoTyPrim   PrimType
 -- rigid typeVars: tyfun arg slots, subsume by comparing INames
 | MonoRigid     IName -- correspond to arguments of type constructors
 | MonoSubTy {
   rigidSubNm :: IName
 , parentTy   :: IName -- case expressions need the parent type info
 , conIndx    :: Int   -- indx of constructor in the data
 }

data PolyType
 = PolyConstrain  [Type] -- (&) multiple typeclass constraints
 | PolyUnion      [Type] -- (|) union types (esp. typeclass var)
 | PolyAny               -- Existential type (flexible typevars)
 -- Data is a polytype (of it's alts)
 | PolyData PolyType DataDef

-- Data saves HNames, so they are reachable from the typeMap
data DataDef
 = DataDef    HName [(HName, [Type])]
-- | RecordDef HName [(HName, [FieldDecl])] -- FieldDecl HName Type
-- | NewTypeDef [IName] DataDef
 | ModuleDef  HName CoreModule
-- data NewType = NewType { parentData :: DataDef , newType :: DataDef }

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
 | TyApp {
   tyFn :: Type
 , tyFnArgsMap :: (IM.IntMap Type) -- type of rigid typeVars in the tyFn
 }

data Fixity = Fixity Int Assoc
data Assoc = LAssoc | RAssoc deriving (Eq)

deriving instance Show PolyType
deriving instance Show DataDef
deriving instance Show Overload
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
deriving instance Show Assoc

data TCError
 = UnifyFail { expected :: Entity, got :: Entity}
 deriving (Show)
