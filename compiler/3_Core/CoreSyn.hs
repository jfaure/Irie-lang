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

{-# LANGUAGE TemplateHaskell #-}
module CoreSyn
where

import Prim

import qualified Data.Vector         as V
import qualified Data.Text           as T
import qualified Data.IntMap.Strict  as IM
import qualified Data.Map.Strict as M
import qualified Data.IntSet as IS
import Control.Lens

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
 , bindings__    :: BindMap
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

-- terms become output code
data Term
 = Var    IName
 | Arg    IName -- lambda-bound (no forall quantifiers)
 | Lit    Literal
 | Instr  PrimInstr [Term] -- must be fully saturated
 | App    Term      [Term]  -- IName [Term]
 | Case   Term      CaseAlts
 | PrimOp PrimInstr

data CaseAlts
 = Switch [(Literal, Term)]
-- | Decon  [(IName, [IName], Term)] -- Con [args] -> expr
-- | Tuple  ([IName], Term)

-- Types are sampled from components of a coproduct of profinite distributive lattices
-- typing schemes contain the (mono | abstract poly)-types of lambda-bound terms
--data TyScheme = TyScheme INameSet TyPlus -- always of the form [D-]t+
type Uni      = Int
type Type     = TyPlus
--data Set = Set Uni Type 
type Set = Type -- with uni annotation ?
type TyCo     = [TyHead] -- same    polarity
type TyContra = [TyHead] -- reverse polarity
type TyMinus  = [TyHead]
type TyPlus   = [TyHead]

-- bisubs always reference themselves, so the m. binding is implicit
type TVar   = ITName
data BiSub  = BiSub { _pSub :: [TyHead] , _mSub :: [TyHead] }
newBiSub    = BiSub [] []
type BiSubs = V.Vector BiSub -- indexed by TVars
-- atomic Bisubstitution:
-- a  <= t- solved by [m- b = a n [b/a-]t- /a-] 
-- t+ <= a  solved by [m+ b = a u [b/a+]t+ /a+] 
-- a  <= c  solved by [m- b = a n [b/a-]c  /a-] -- (or equivalently,  [a u b /b+])

-- components of the profinite distributive lattice of types
data TyHead -- head constructors for types.
 -- primitives (directly type terms)
 = THPrim     PrimType
 | THVar      TVar       -- index into bisubs
 | THArrow    [TyContra] TyCo
 | THRec      IName TyCo -- guarded and covariant in a 
   -- (ie. `Ma. (a->bool)->a` ok, but not `Ma. a->Bool`)
 | THData     SumOfRecord -- tCO
 | THAlias    IName       -- index into bindings

 -- calculus of constructions
 | THArg      IName         -- lambda bound
 -- Apps
 | THIxType   Type Type
 | THIxTerm   Type (Term , Type)
 | THEta      Term Type -- term is a universe polymorphic function

 | THHigher   Uni -- what universe something is in

data THArg
 = THArgType [TyHead]
 | THArgTerm Term

data SumOfRecord = SumOfRecord [(SLabel , [(PLabel , TyCo)])]

data Kind -- the type of types: labels for different head constructors
 = KPrim -- int | float
 | KArrow
 | KVar
 | KPi   -- generalization of KArrow (with possible pi binder)
 | KData

-- tagged tt
data Expr
 = Core Term Type
 | Ty   Set

data Bind
 = WIP
 | E [IName] Term -- eta expansion (universe polymorphic operation)
 | B [IName] Term Type -- a term binding
 | T [TArg]  Set       -- a type binding

data TArg -- argument to type function
 = ArgEta  IName
 | ArgTerm IName
 | ArgType Uni IName

makeLenses ''BiSub

-- Notes --
{-   The lambda-bound types here are flexible ie. subsumption can occur before beta-reduction.
  This can be weakened by instantiation to a (monomorphically abstracted) typing scheme
  We unconditionally trust annotations so far as the rank of polymorphism, since that cannot be inferred (we cannot insert type abstractions)
-}

deriving instance Show Expr
deriving instance Show Bind
deriving instance Show TArg
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

deriving instance Eq SumOfRecord
--deriving instance Eq MonoType
--deriving instance Eq PolyType
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
