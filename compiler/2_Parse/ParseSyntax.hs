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

-- externs can't be checked (eg. syscalls / C apis etc..)
data ImportDecl
 = Extern   { externName :: HName , externType :: PrimType }
 | ExternVA { externName :: HName , externType :: PrimType }
 | Import  HName -- a record
 | NoScope HName -- temporarily out of scope

data Fixity = Fixity Assoc (Maybe Int) [Op] -- info for infix operators
data Assoc = AssocNone | AssocLeft | AssocRight

data Module = Module {
   _moduleName :: HName

 , _imports    :: [ImportDecl]
 , _bindings   :: [TopBind] -- top binds
 , _locals     :: [TopBind] -- locals (not incl. args)

 , _parseDetails :: ParseDetails
}

type NameMap = Data.Map.Map HName IName
data ParseDetails = ParseDetails {
   _hNameBinds    :: NameMap
 , _hNameArgs     :: NameMap
 , _hNamesNoScope :: NameMap
 , _fields        :: NameMap
 , _labels        :: NameMap
-- , fixities     :: V.Vector Fixity
}

data TopBind = FunBind HName [FnMatch] (Maybe TT)
data FnMatch = FnMatch [Pattern] TT

data TTName
 = VBind   IName
 | VLocal  IName
 | VExtern IName
 | VQual   [IName] IName

-- Parser Expressions (types and terms are syntactically equivalent)
data TT
 = Var TTName
 | WildCard -- "_"

 -- lambda-calculus
 | App TT [TT]
 | InfixTrain TT [(TT, TT)] -- `name` or symbolName

 -- other tt primitives (sum , product , list)
 | Cons   [(FName , TT)]
 | Proj   TT FName
 | Label  LName TT
 | Match  [(LName , Pattern , TT)]
 | List   [TT]

 -- term primitives
 | Lit     Literal
 | MultiIf [(TT, TT)]

 -- type primitives
 | TyLit    PrimType
 | TyArrow  [TT] -- type of an Abs

 | Typed    { t :: TT , typeOf :: TT }

-- patterns represent arguments of abstractions
data Pattern
 = PArg  IName -- introduce VLocal arguments
 | PLit  Literal
 | PWildCard
 | PTyped Pattern TT
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
    , "extern: " ++ show (p^.hNamesNoScope)
    , "fields: " ++ show (p^.fields)
    , "labels: " ++ show (p^.labels)
    ]
deriving instance Show TopBind
deriving instance Show ImportDecl
instance Show TTName where
  show = \case
    VBind x   -> "π" ++ show x 
    VLocal  x -> "λ" ++ show x
    VExtern x -> "E" ++ show x
    VQual a b -> show a ++ "." ++ show b
deriving instance Show Fixity
deriving instance Show Assoc
deriving instance Show FnMatch 
deriving instance Show TT
deriving instance Show Pattern
