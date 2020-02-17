{-# LANGUAGE LambdaCase, ScopedTypeVariables , MultiWayIf , StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module ParseSyntax where -- import qualified as PSyn

import Prim
import Data.Text as T -- Names are Text (ShortText ?)
import qualified Data.Map
import qualified Data.Vector as V
import Control.Lens

type IName = Int
type HName = Text
type FName = IName -- record  fields
type LName = IName -- sumtype labels

type Op = IName
type ImportDecl = IName
-- externs can't be checked (eg. syscalls / C apis etc..)
data Extern = Extern IName PrimType | ExternVA IName PrimType

data Fixity = Fixity Assoc (Maybe Int) [Op] -- info for infix operators
data Assoc = AssocNone | AssocLeft | AssocRight

data Module = Module {
   _moduleName :: HName

 , _imports    :: [ImportDecl]
-- , _externs    :: [Extern]
 , _bindings   :: [TopBind] -- top binds
 , _locals     :: [TopBind] -- locals (incl args)

 , _parseDetails :: ParseDetails
}

type NameMap = Data.Map.Map HName IName
data ParseDetails = ParseDetails {
   _hNameBinds   :: NameMap
 , _hNameArgs    :: NameMap
 , _hNameImports :: NameMap
 , _fields       :: NameMap
 , _labels       :: NameMap
-- , fixities     :: V.Vector Fixity
}

data TopBind
 = FunBind    [FnMatch] (Maybe TT)
 | ExternBind Extern
data FnMatch = FnMatch { fnArgs :: [Pattern] , expr :: TT }

-- Parser Expressions (types and terms are syntactically equivalent)
data TT
 -- vars
 = VBind   IName -- top-bound
 | VLocal  IName -- (lambda, let)-bound
 | VExtern IName -- imported (aka. not in scope)
 | WildCard -- "_" as an expression

 -- lambda-calculus
 | Abs FnMatch   -- can we eagerly lift type abstractions ? TODO
 | App TT [TT]
 | InfixTrain TT [(IName, TT)] -- `name` or symbolName (must be resolved later, when we have fixities)

 -- Constructions (sum , product , list) types
 | Cons   [(FName , TT)]
 | Proj   TT FName
 | Label  LName TT
 | Match  [(LName , TT)]
 | List   [TT]

 -- term primitives
 | Lit    Literal
 | PrimOp PrimInstr
 | MultiIf [(TT, TT)]

 -- type primitives (Terms aren't allowed here, eg. `Int -> 3` is nonsense)
 | TyPrim   PrimType
 | TyArrow  [TT]

 | Typed    { t :: TT , typeOf :: TT }

-- patterns represent arguments of abstractions
data Pattern
 = PArg  IName -- introduce VLocal arguments
 | PLit  Literal
 | PWildCard
 | PTyped Pattern TT
 -- rank-n patterns ?
-- | PAs   IName Pattern
-- | match sum-of-product ?

makeLenses ''Module
makeLenses ''ParseDetails

showL ind = Prelude.concatMap $ (('\n' : ind) ++) . show
instance Show Module where
  show m = show (m^.moduleName) ++ " {\n"
    ++ "imports: " ++ showL "  " (m^.imports)  ++ "\n"
    ++ "binds:   " ++ showL "  " (m^.bindings) ++ "\n"
    ++ "locals:  " ++ showL "  " (m^.locals)   ++ "\n"
    ++ show (m^.parseDetails) ++ "\n}"
instance Show ParseDetails where
  show p = Prelude.concatMap ("\n  " ++) 
    [ "binds:  " ++ show (p^.hNameBinds)
    , "args:   " ++ show (p^.hNameArgs)
    , "extern: " ++ show (p^.hNameImports)
    , "fields: " ++ show (p^.fields)
    , "labels: " ++ show (p^.labels)
    ]
deriving instance Show TopBind
deriving instance Show Fixity
deriving instance Show Assoc
deriving instance Show Extern
deriving instance Show FnMatch 
deriving instance Show TT
deriving instance Show Pattern
