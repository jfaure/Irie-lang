-- vs Core:
-- - no state (qnames/typeclasses...)
-- - PSyn has infix operators
-- - PSyn delays figuring out applications/infix applications

module ParseSyntax where -- import qualified as PSyn

import Prim
import Data.Text as T -- Names are Text
import qualified Data.Vector as V

data Name        -- variables (incl constructors and symbols)
 = Ident  Text -- varid/conid
 | Symbol Text -- varsym/consym
data QName -- QName: qualified name: '::' namespace operator
 = QName [Name] Name
 | UnQual Name
 | ExprHole --
type Op = Name
type QOp = QName

-- modules as extensions of records ?
-- So they can be returned by type functions
data Module = Module {
   moduleName :: Name
-- , decls      :: [Decl]
 , parseTree  :: ParseTree
}

data ImportDecl
 = Open    Name -- open import
 | Require Name -- qualified import
 | ImportAs ImportDecl Name
 | ImportCustom {
   importMod :: Name
 , hiding    :: [Name]
 , renaming  :: [(Name, Name)]
 }
 -- | Extern | ExternVA

data Decl
 = Import        ImportDecl
 -- type decls
 | TypeAlias     Name Type          -- note. type includes data
 | TypeFun       Name [Name] PExp   -- TODO move this to Type
 | TypeClass     Name [Name] [Decl] -- haskell newtype ?
 | TypeClassInst Name Name   [Decl]

 -- top bindings (seperate because sigs may be in sigModules)
 | Extern        Name Type
 | ExternVA      Name Type
 | TypeSigDecl   [Name] Type
 | FunBind       [Match]

 -- auxilary decls
 | InfixDecl     Assoc (Maybe Int) [Op] --info for infix operators
 | DefaultDecl   Type Type -- eg: default Num Integer

-- associativity of infix/infixr/infixl decls
data Assoc = AssocNone | AssocLeft | AssocRight
newtype Binds = BDecls [Decl] -- let or where clauses
data Match -- clauses of a function binding
 = Match Name [Pat] Rhs
 | InfixMatch Pat Name [Pat] Rhs
 | TypeMatch Name Rhs -- f : Int->Float = cast -- TODO
data Rhs
 = UnGuardedRhs PExp
 | GuardedRhss [GuardedRhs]
data GuardedRhs = GuardedRhs [Stmt] PExp

-- note. Types may be parsed as TyFunction if they take arguments
data Type
 = TyPrim PrimType -- primitive
 | TyPoly PolyType
-- | TyQuant [Name] [Name] Type -- quantified (forall ::)

 | TyName Name    -- alias / data name / binding (TyExpr)
 | TyVar  Name    -- introduced by TyFunction

 | TyArrow [Type] -- function type
 | TyApp Type [Type]

 -- GADTs
 -- These must subsume Type so they can be returned by TyFunctions
 | TyRecord [(Name, Record)]
-- | TyData   [(Name, [Type])]
 | TyInfixData Type Name Type
 | TyModule Module

 | TyExpr PExp       -- type functions (maybe dependent on values)
 | TyTyped Type Type -- user gave a type (kind?) annotation
 | TyUnknown         -- including '_' type given / no type sig
-- type DataDef = Type -- TyRecord, TyData, TyInfixData
data Record
  = RecordTuple  [Type]
  | RecordFields [(Name, Type)]
-- type RecordField = (Name, Type)

data PolyType
 = PolyAnd   [Type] -- & constraints
 | PolyUnion [Type] -- | constraints
 | PolyAny          -- existential type

-- Parser Expressions
data PExp
 = Var QName
 | Con QName
 | Lit Literal
 | PrimOp PrimInstr
-- | Infix QName     -- `name` or symbols
 | App PExp [PExp]
 | InfixTrain PExp [(QName, PExp)] -- `name` or symbolName
 | Lambda [Pat] PExp
 | SectionL PExp QName -- operator sections
 | SectionR QName PExp
 | Let Binds PExp
-- | Let Module PExp
 | Rec Module PExp
 | MultiIf [(PExp, PExp)] -- ghc accepts [GuardedRhs]
 | Case PExp [Alt]
 | LambdaCase [Alt]
 | AsPat Name Pat
 | WildCard -- "_" as an expression

 | TypeExp Type -- first class types.
 | Typed Type PExp -- user supplied type annotation

data Alt = Alt Pat Rhs -- (Maybe Binds) -- case alternatives

data Pat
 = PVar Name
 | PLit Literal
 | PInfixApp Pat QName Pat
 | PApp QName [Pat]
 | PTuple [Pat]
 | PList [Pat]
 | PWildCard

data Stmt -- in 'do' / in pattern guard
 = Generator Pat PExp -- pat <- exp
 | Qualifier PExp -- exp alone in do expr
 | LetStmt   Binds

-- subtyping would be nice, but in the meantime I won't make a data
-- for every single subtype
data ParseTree = ParseTree {
   tyAliases  :: V.Vector Decl
 , tyFuns     :: V.Vector Decl
 , classes    :: V.Vector Decl
 , classInsts :: V.Vector Decl
 , topSigs    :: V.Vector Decl
 , topBinds   :: V.Vector Decl
 , fixities   :: V.Vector Decl
 , defaults   :: V.Vector Decl
 , externs    :: V.Vector Decl
 , modImports :: V.Vector Decl
}

deriving instance Show Name
deriving instance Show QName 
deriving instance Show Module
deriving instance Show ParseTree
deriving instance Show Decl
deriving instance Show ImportDecl
deriving instance Show Assoc
deriving instance Show Binds
deriving instance Show Match 
deriving instance Show Rhs
deriving instance Show GuardedRhs
deriving instance Show Type
deriving instance Show Record
deriving instance Show PolyType
deriving instance Show PExp
deriving instance Show Alt
deriving instance Show Pat
deriving instance Show Stmt
