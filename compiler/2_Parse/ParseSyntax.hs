-- vs Core:
-- - no state (qnames/typeclasses...)
-- - PSyn has infix operators
-- - PSyn delays figuring out applications/infix applications

module ParseSyntax where -- import qualified as PSyn

import Prim
import qualified Data.Text as T

type Module = [Decl]

-- TODO use bytestring for names?
-- QName: qualified name: '::' namespace operator
data QName
 = QName [Name] Name
 | UnQual Name
 | ExprHole --
data Name -- variables (incl constructors and symbols)
 = Ident  String -- varid/conid
 | Symbol String -- varsym/consym
type QOp = QName
type Op = Name

-- top level
-- data Module {
--    mName    :: Name
--  , contents :: Decl.DataDecl -- modules are functors, namespaced in a data
--  }
data Decl
 -- type decls 
 -- newtype necessary for classes ?
 = TypeAlias     Name Type        -- incl. data
 | TypeFun       Name [Name] PExp
 | TypeClass     Name [Decl]
 | TypeClassInst Name Name [Decl] -- instance declaration

 -- top bindings
 | TypeSigDecl   [Name] Type
 | FunBind       [Match]  -- TODO scoped type variables ?

 -- auxilary decls
 | InfixDecl     Assoc (Maybe Integer) [Op] --info for infix operators
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

type Kind = Type
-- note. Types may be parsed as TyFunction if they take arguments
data Type
 = TyPrim PrimType -- primitive
 | TyForall Forall

 | TyName Name    -- alias / data name / binding (TyExpr)
 | TyVar  Name    -- introduced by TyFunction

 | TyArrow [Type] -- function type

 -- GADTs
 -- These must subsume Type so they can be returned by TyFunctions
 | TyRecord [(Name, [(Name, Type)])]
 | TyData   [(Name, [Type])]
 | TyInfixData Type Name Type -- TODO

 | TyExpr PExp       -- type functions (maybe dependent on values)
 | TyTyped Type Type -- user gave a 'Kind' annotation (are all kinds types ?)
 | TyUnknown         -- including '_' type given / no type sig
type DataDef = Type -- TyRecord, TyData, TyInfixData

data Forall
 = ForallAnd [Type] -- & constraints
 | ForallOr  [Type] -- | constraints
 | ForallAny        -- existential type

-- Parser Expressions
data PExp
 = Var QName
 | Con QName
 | Lit Literal
 | PrimOp PrimInstr
 | Infix QName     -- `name`
 | App PExp [PExp] -- extract infix apps from this during core2expr
 | Lambda [Pat] PExp
 | Let Binds PExp
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

deriving instance Show QName 
deriving instance Show Name 
deriving instance Show Decl
deriving instance Show Assoc
deriving instance Show Binds
deriving instance Show Match 
deriving instance Show Rhs
deriving instance Show GuardedRhs
deriving instance Show Type
deriving instance Show Forall
deriving instance Show PExp
deriving instance Show Alt
deriving instance Show Pat
deriving instance Show Stmt
