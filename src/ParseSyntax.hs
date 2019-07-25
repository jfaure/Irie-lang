{-# LANGUAGE StandaloneDeriving #-}

module ParseSyntax where -- import qualified as PSyn
-- Parser expresssions
-- Note. Syntax for the desugared language
-- vs Core:
-- - no state (qnames/typeclasses...)
-- - PSyn has infix operators
-- - PSyn delays figuring out applications/infix applications

import qualified Data.Text as T
import qualified LLVM.AST

-- QName: qualified name: '::' namespace operator
data QName -- (maybe) `.` qualified variables/constructors/symbols
 = QName [Name] Name
 | UnQual Name
 | ExprHole -- _
data Name -- variables (incl constructors and symbols)
 = Ident  String -- varid/conid
 | Symbol String -- varsym/consym
type QOp = QName
type Op = Name

-- top level
type Module = [Decl]
data Decl
 = TypeAlias     Name Name
 | DataDecl      Name Kind [QualConDecl] --incl GADTS

 | InfixDecl     Assoc (Maybe Integer) [Op] -- ?
 | TypeSigDecl   [Name] Type
 | FunBind       [Match]

 | TypeClassDecl Name [ClassDecl]
 | InstDecl      (Maybe Overlap) InstRule [InstDecls]
 | DefaultDecl   Type Type -- eg: default Num Integer

-- associativity of infix/infixr/infixl decls
data Assoc = AssocNone | AssocLeft | AssocRight
data InstRule = IRule Foralls InstHead -- part before `where`
data InstHead
 = IHCon QName        -- normal constructor
 | IHInfix Type QName -- infix

newtype Binds = BDecls [Decl] -- let or where clauses

data Match -- clauses of a function binding (sugar for 'case')
 = Match Name [Pat] Rhs (Maybe Binds)
 | InfixMatch Pat Name [Pat] Rhs (Maybe Binds)

data QualConDecl = QualConDecl Foralls {- => -} ConDecl
data ConDecl -- data constructor
 = ConDecl Name [Type]
 | InfixConDecl Type Name Type
 | GadtDecl Name Kind Foralls {- => -} [FieldDecl]
data FieldDecl = FieldDecl Name Type

-- note no type/data family nonsense .. we have dependent types
data ClassDecl
 = ClsDecl Decl
 | ClsDefSig Name Type -- default signature
data InstDecls
 = InstDecls Decl
 | InstType Type Type
 | InstData Type [QualConDecl]

data Overlap -- recognized overlap (pragmas)
 = NoOverlap | Overlap
 | Overlapping | Overlaps | Overlappable | Incoherent

data Rhs
 = UnGuardedRhs PExp
 | GuardedRhss [GuardedRhs]
data GuardedRhs = GuardedRhs [Stmt] PExp

-- Types: in general these are all erased at runtime,
-- and serve only to improve compile-time correctness
-- However, if you use (a -> 'a) functions in expressions,
-- part of the type must become runtime data.
-- Note that (Type:Type) only in the compiler
type Kind = Type
data Type
 = TyLlvm LLVM.AST.Type
 | TyForall Foralls Type
 | TyOr [Type]  -- sum constraints     (T <= T0 | T1)
 | TyAnd [Type] -- product constraints (T <= T0 & T1)
 | TyVar TyVarBind -- type variable
 | TyLifted PExp -- value level expression
 | TyUnknown
data TyVarBind = TyVarBind Name Kind
type Foralls = [TyVarBind]

data Literal
 = Char Char
 | String String
 | Int Integer
 | Frac Rational

-- Parser Expressions
-- Note! we must defer parsing infix applications: we may not
-- have all user infix decls and precedences immediately
-- also we don't want the parser to be stateful
-- So we defer a pass over 'App' to extract InfixApps.
data PExp
 = Var QName
 | Con QName -- ?
 | Lit Literal
 | Infix QName -- `name`
 | App PExp [PExp] -- extract infix apps from this later
 | Lambda [Pat] PExp
 | Let Binds PExp
 | MultiIf [(PExp, PExp)] -- ghc accepts [GuardedRhs]
 | Case PExp [Alt]
 | Do [Stmt]
 | MDo [Stmt]
 | List [PExp]
 | TypeSig PExp Type
 | AsPat Name Pat

 -- first class types. If this is present in expr arguments that
 -- depend on a runtime value, then it is a 'pi' type,
 -- and must become part of the runtime data.
 | TypeExp Type
 | WildCard -- "_" as an expression

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
deriving instance Show InstRule
deriving instance Show InstHead
deriving instance Show Overlap 
deriving instance Show Binds
deriving instance Show Match 
deriving instance Show QualConDecl
deriving instance Show ConDecl 
deriving instance Show FieldDecl
deriving instance Show ClassDecl
deriving instance Show InstDecls
deriving instance Show Rhs
deriving instance Show GuardedRhs
deriving instance Show Type
deriving instance Show TyVarBind
deriving instance Show Literal
deriving instance Show PExp
deriving instance Show Alt
deriving instance Show Pat
deriving instance Show Stmt 
