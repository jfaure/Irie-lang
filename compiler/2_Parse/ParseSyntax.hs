-- Parser expresssions
-- vs Core:
-- - no state (qnames/typeclasses...)
-- - PSyn has infix operators
-- - PSyn delays figuring out applications/infix applications

module ParseSyntax where -- import qualified as PSyn

import qualified Data.Text as T
import qualified LLVM.AST

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

data Literal = Char Char | Int Integer | Frac Rational | String String

-- top level
-- data Module { 
--    mName    :: Name
--  , contents :: Decl.DataDecl -- modules are functors, namespaced in a data
--  }
type Module = [Decl]
data Decl
 = TypeAlias     Name Type
 | DataDecl      Name Kind [QualConDecl] --incl GADTS
 | TypeFun       Name [Name] PExp -- CoreExpr.TyExpr TODO

 | TypeSigDecl   [Name] Type
 | FunBind       [Match]  -- TODO scoped type variables ?

 | InfixDecl     Assoc (Maybe Integer) [Op] --info for infix operators
 | DefaultDecl   Type Type -- eg: default Num Integer

-- associativity of infix/infixr/infixl decls
data Assoc = AssocNone | AssocLeft | AssocRight
newtype Binds = BDecls [Decl] -- let or where clauses
data Match -- clauses of a function binding
 = Match Name [Pat] Rhs
 | InfixMatch Pat Name [Pat] Rhs
 | TypeMatch Name Rhs -- f : Int->Float = cast -- TODO

-- TODO parse `data` as a type ? that would give us type functions etc..
data QualConDecl = QualConDecl TyVars ConDecl
data ConDecl -- data constructor
 = ConDecl Name [Type]
 | InfixConDecl Type Name Type
 | GadtDecl Name Kind TyVars [FieldDecl]
data FieldDecl = FieldDecl Name Type

data Rhs
 = UnGuardedRhs PExp
 | GuardedRhss [GuardedRhs]
data GuardedRhs = GuardedRhs [Stmt] PExp

type Kind = Type
-- note. Types may be parsed as TyFunction if they take arguments
data Type
 = TyLlvm LLVM.AST.Type
 | TyForall Forall

 | TyName Name    -- alias / data name / binding (TyExpr)
 | TyVar  Name    -- introduced by TyFunction

 | TyArrow [Type] -- function

 -- data. GADT style is used exclusively
 | TyRecord Name [(Name, [Type])]
 | TyData   Name [Type]
 | TyInfixData Type Name Type

 | TyExpr PExp       -- type functions (maybe dependent on values)
 | TyTyped Type Type -- user gave a 'Kind' annotation (are all kinds types ?)
 | TyUnknown         -- including '_' type given / no type sig

data Forall
 = ForallAnd [Type] -- & constraints
 | ForallOr  [Type] -- | constraints
 | ForallAny -- basically ~ an opaque monotype (eg. len : [a]->Int)

type TyVars = [Name]

-- Parser Expressions
-- Note! we must defer parsing infix applications: we may not
-- have all user infix decls and precedences immediately
data PExp
 = Var QName
 | Con QName
 | Lit Literal
 | Infix QName -- `name`
 | App PExp [PExp] -- extract infix apps from this later
 | Lambda [Pat] PExp
 | Let Binds PExp
 | MultiIf [(PExp, PExp)] -- ghc accepts [GuardedRhs]
 | Case PExp [Alt]
 | LambdaCase [Alt] -- function for case of
 | Do [Stmt]
 | MDo [Stmt]
 | List [PExp]
 | TypeSig PExp Type
 | AsPat Name Pat
 | WildCard -- "_" as an expression

 -- first class types.
 -- if it depends on a runtime value, then it is a 'pi' type,
 | TypeExp Type
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
deriving instance Show QualConDecl
deriving instance Show ConDecl 
deriving instance Show FieldDecl
deriving instance Show Rhs
deriving instance Show GuardedRhs
deriving instance Show Type
deriving instance Show Forall
deriving instance Show Literal
deriving instance Show PExp
deriving instance Show Alt
deriving instance Show Pat
deriving instance Show Stmt 
