{-# LANGUAGE TemplateHaskell , DeriveGeneric #-}
{-# OPTIONS  -funbox-strict-fields #-}

module ParseSyntax where -- import qualified as PSyn

import Prim
import Data.Text as T -- Names are Text (ShortText ?)
import qualified Data.Map as M
import qualified Data.HashMap.Strict as HM
import qualified Data.Vector as V
import Control.Lens

type IName = Int
type HName = Text
type FName = IName -- record  fields
type LName = IName -- sumtype labels
type ImplicitArg = (IName , Maybe TT) -- implicit arg with optional type annotation

data MixFixName = MFHole | MFName HName deriving (Show , Eq)
type MixFixDef = [MixFixName]

data Fixity = Fixity Assoc (Maybe Int) [IName]
data Assoc = AssocNone | AssocLeft | AssocRight

data ImportDecl -- extern type ann can't be checked (eg. syscalls / C apis etc..)
 = Extern   { externName :: HName , externType :: TT }
 | ExternVA { externName :: HName , externType :: TT }

data Module = Module {
   _moduleName :: HName

 , _imports    :: [HName]
 , _externFns  :: [ImportDecl]
 , _bindings   :: [TopBind] -- top binds

 , _parseDetails :: ParseDetails
}

type NameMap = M.Map HName IName
data ParseDetails = ParseDetails {
 -- Note. mixFixDefs stored in these maps are partial:
 -- for mf, the first, and for postfixes the first 2 elems of the mixfixdef list are implicit
   _mixFixDefs    :: M.Map HName [(MixFixDef , TTName)] -- all mixfixDefs starting with a name
 , _postFixDefs   :: M.Map HName [(MixFixDef , TTName)] -- mixfixes starting with _
 , _hNameBinds    :: (Int , NameMap) -- count anonymous args (>= nameMap size)
 , _hNameLocals   :: [NameMap] -- let-bound
 , _hNameArgs     :: [NameMap]
 , _nArgs         :: Int
 , _hNamesNoScope :: NameMap
 , _fields        :: NameMap
 , _labels        :: NameMap
-- , fixities     :: V.Vector Fixity
}

data TopBind = FunBind HName [ImplicitArg] [FnMatch] (Maybe TT)
data FnMatch = FnMatch [ImplicitArg] [Pattern] TT

data TTName
 = VBind   IName
 | VLocal  IName
 | VExtern IName

-- Parser Expressions (types and terms are syntactically equivalent)
data TT
 = Var !TTName
 | WildCard -- "_"

 -- lambda-calculus
 | App TT [TT]
 | InfixTrain TT [(TT, TT)] -- precedence unknown

 -- tt primitives (sum , product , list)
 | Cons   [(FName , TT)] -- can be used to type itself
 | Proj   TT FName
 | Label  LName [TT]
 | Match  [(LName , [Pattern] , TT)]
 | List   [TT]
-- | TySum  [(LName , [TT])]
 | TySum [(LName , [ImplicitArg] , TT)] -- function signature
 | TyListOf TT

 -- term primitives
 | Lit     Literal
 | LitArray [Literal]
 | MultiIf [(TT, TT)] TT -- if .. elseif .. else

-- patterns represent arguments of abstractions
data Pattern
 = PArg  IName -- introduce VLocal arguments
 | PTT   TT
 | PApp  Pattern [Pattern]
-- | PLit  Literal
-- | PWildCard
-- | PTyped Pattern TT
-- | PAs   IName Pattern
-- | match sum-of-product ?

makeLenses ''Module
makeLenses ''ParseDetails

showL ind = Prelude.concatMap $ (('\n' : ind) ++) . show
instance Show Module where
  show m = show (m^.moduleName) ++ " {\n"
    ++ "imports: " ++ showL "  " (m^.imports)  ++ "\n"
    ++ "binds:   " ++ showL "  " (m^.bindings) ++ "\n"
--  ++ "locals:  " ++ showL "  " (m^.locals)   ++ "\n"
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
deriving instance Show Fixity
deriving instance Show Assoc
deriving instance Show FnMatch 
deriving instance Show TT
deriving instance Show Pattern
