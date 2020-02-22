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

module CoreSyn
where

import Prim

import qualified Data.Vector         as V
import qualified Data.Text           as T
import qualified Data.IntMap.Strict  as IM
import qualified Data.Map.Strict as M
import qualified Data.IntSet as IS

type HName    = T.Text -- human readable name
type IName    = Int    -- Int name: index into bind|type vectors
type ITName   = IName  -- IName of a type
type SLabel   = IName  -- IName for labels
type PLabel   = IName
type INameSet = IS.IntSet

type TypeMap = V.Vector Entity
type BindMap = V.Vector Binding
type IMap    = IM.IntMap -- bind iname map
type ITMap   = IM.IntMap -- type iname map

data ImportList     = ImportList [CoreModule]
data CoreModule     = CoreModule {
   moduleName  :: HName

 , algData     :: TypeMap -- data and aliases
 -- binds: constructors, locals, and class Fns (+ overloads!)
 , bindings    :: BindMap
 , nTopBinds   :: Int -- number of relevent binds in the bindMap

 , parseDetails   :: ParseDetails
}

-- info for parsing files importing this module / the repl
data ParseDetails = ParseDetails {
   _classDecls :: V.Vector ClassDecl -- so importers can check instances
-- , _defaults   :: IM.IntMap MonoType
 , _fixities   :: M.Map HName Fixity
 -- HName lookup tables
 , _hNameBinds :: M.Map HName IName
 , _hNameTypes :: M.Map HName IName
}
-- TODO rm
hNameBinds = _hNameBinds . parseDetails
hNameTypes = _hNameTypes . parseDetails

data Fixity = Fixity Int Assoc
data Assoc = LAssoc | RAssoc deriving (Eq, Show)
data ClassDecl = ClassDecl {
   className :: HName
 , classFns  :: V.Vector ClassFn
 , supers    :: [HName]
}
data ClassFn = ClassFn {
   classFnInfo :: Entity      -- TODO use TyFunction
 , defaultFn   :: Maybe IName -- jointype or instance type ??
}

data TypeAnn = TyNone | TyUser Type | TyJudged TyPlus
-- an entity = info about anything we give an IName to.
data Entity = Entity { -- entity info
   named    :: Maybe HName
 , ty       :: TypeAnn
 , source   :: SourceEntity
 }
ent = Entity Nothing TyNone Export
data SourceEntity = Export | Import | Private | ThisModule

data Binding
 = LBind { -- let binding
   info  :: Entity  -- hname, type, source
 , args  :: [IName] -- the unique argINames used locally by
 , expr  :: Term
 }
 | LetType {
   uni     :: Uni
 , info    :: Entity
 , args    :: [IName]
 , typeAbs :: TyPlus
 }
 | LArg   { info :: Entity }  -- lambda-bound
 | LNoScope { info :: Entity }
 -- always inline this binding (to access freevars)
 -- only used internally for pattern match deconstructions
 | Inline { info :: Entity , expr :: Term }
 | LInstr { info :: Entity , instrBind :: PrimInstr } -- instrs need a type annotation
 | LCon   { info :: Entity } --Term level GADT constructor
 | LExtern{ info :: Entity }
 | LClass {
   info        :: Entity -- TypeFunction
 , classNm     :: HName  -- change to IName ?
 , overloads   :: ITMap IName -- instanceIds
 }

data Term
 = Var    IName
 | Arg    IName -- lambda-bound (no forall quantifiers)
 | Lit    Literal
 | Instr  PrimInstr [Term] -- must be fully saturated
 | App    IName     [Term]
 | Case   Term      CaseAlts

data CaseAlts
 = Switch [(Literal, Term)]
-- | Decon  [(IName, [IName], Term)] -- Con [args] -> expr
-- | Tuple  ([IName], Term)

-- Types are sampled from components of a coproduct of profinite distributive lattices
-- typing schemes contain the (mono | abstract poly)-types of lambda-bound terms
--data TyScheme = TyScheme INameSet TyPlus -- always of the form [D-]t+
type Uni      = Int
data Type     = Type Uni TyPlus
type TCo      = [TyHead] -- same    polarity
type TContra  = [TyHead] -- reverse polarity
type TyMinus  = [TyHead]
type TyPlus   = [TyHead]

-- bisubs always reference themselves, so the m. binding is implicit
type TVar   = ITName
data BiSub  = BiSub { pSub :: [TyHead] , mSub :: [TyHead] }
type BiSubs = V.Vector BiSub -- indexed by TVars
-- atomic Bisubstitution:
-- a  <= t- solved by [m- b = a n [b/a-]t- /a-] 
-- t+ <= a  solved by [m+ b = a u [b/a+]t+ /a+] 
-- a  <= c  solved by [m- b = a n [b/a-]c  /a-] -- (or equivalently,  [a u b /b+])

-- components of the profinite distributive lattice of types
data TyHead -- head constructors for types.
 = THPrim     PrimType
 | THAlias    ITName
 | THVar      TVar       -- individial typevars are 'atomic' components of the type lattice
 | THArrow    [TContra] TCo
 | THRec      ITName TCo -- guarded and covariant in a (ie. `Ma. (a->bool)->a` ok, but not `Ma. a->Bool`)
 | THData     SumOfRecord -- tCO

 | THLam      ITName TyHead
 | THIndexed  ITName Term
 | THArg      ITName

data SumOfRecord = SumOfRecord [(SLabel , [(PLabel , TCo)])]

data Kind -- label for different head constructors
 = KPrim -- int | float
 | KArrow
 | KVar
 | KPi   -- generalization of KArrow (with possible pi binder)
 | KData

-- Notes --
{- THLam: parametrised type operators. notice this makes the order of lambda-bound types (somewhat) relevant
  The lambda-bound types here are flexible ie. subsumption can occur before beta-reduction.
  This can be weakened by instantiation to a (monomorphically abstracted) typing scheme
  We unconditionally trust annotations so far as the rank of polymorphism, since that cannot be inferred
  ie. we cannot insert uses of THLam
-}

deriving instance Show ClassDecl
deriving instance Show ClassFn
deriving instance Show Binding
--deriving instance Show DataDef
--deriving instance Show PolyType
--deriving instance Show MonoType
--deriving instance Show Type
deriving instance Show Term
deriving instance Show BiSub
deriving instance Show CaseAlts
deriving instance Show Entity
deriving instance Show SourceEntity
deriving instance Show ParseDetails
deriving instance Show CoreModule
deriving instance Show Fixity
deriving instance Show TyHead
deriving instance Show Kind
deriving instance Show SumOfRecord
deriving instance Show TypeAnn
deriving instance Show Type

deriving instance Eq SumOfRecord
--deriving instance Eq MonoType
--deriving instance Eq PolyType
--deriving instance Eq Type
--deriving instance Eq DataDef
deriving instance Eq TyHead
deriving instance Eq Kind
deriving instance Eq ClassDecl
deriving instance Eq ClassFn
deriving instance Eq Binding
deriving instance Eq BiSub
deriving instance Eq Term
deriving instance Eq CaseAlts
deriving instance Eq Entity
deriving instance Eq SourceEntity
deriving instance Eq ParseDetails
deriving instance Eq CoreModule
deriving instance Eq Fixity
deriving instance Eq TypeAnn
deriving instance Eq Type
