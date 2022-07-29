{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS  -funbox-strict-fields #-}
module ParseSyntax where
import Prim ( Literal )
import QName ( QName )
import MixfixSyn ( MFWord, MixfixDef )
import Control.Lens ( (^.), makeLenses )
import Text.Megaparsec.Pos ( Pos )
import qualified Data.Map.Strict as M ( Map )

type FName        = IName -- record  fields
type LName        = IName -- sumtype labels
type FreeVar      = IName -- non-local argument
type FreeVars     = BitSet
type NameMap      = M.Map HName IName
type SourceOffset = Int

data Module = Module { -- Contents of a File (Module = Function : _ → Record | Record)
   _moduleName  :: HName -- the fileName

 , _imports     :: [HName] -- all imports used at any scope
 , _bindings    :: [FnDef] -- hNameBinds (! these are listed in reverse)

 , _parseDetails :: ParseDetails
}

-- args and signature for the module (return type must be a record)
-- data FunctorModule = FunctorModule [Pattern] (Maybe TT) SourceOffset

-- HNames and local scope
data ParseDetails = ParseDetails {
   _hNameBinds     :: (Int , NameMap) -- also count anonymous (lambdas) (>= nameMap size)
 , _hNameLocals    :: [NameMap] -- let-bound names stack
 , _hNameArgs      :: [NameMap]
 , _hNameMFWords   :: (Int , M.Map HName [MFWord]) -- keep count to handle overloads (bind & mfword)
 , _freeVars       :: FreeVars
 , _underscoreArgs :: FreeVars
 , _nArgs          :: Int
 , _hNamesNoScope  :: NameMap
 , _fields         :: NameMap
 , _labels         :: NameMap
 , _newLines       :: [Int]
}
data FnDef = FnDef {
   fnNm         :: HName
 , fnRecType    :: !LetRecT        -- or mutual
 , fnMixfixName :: Maybe MixfixDef -- rm (mixfixes are aliases)
 , fnFreeVars   :: FreeVars
 , fnMatches    :: NonEmpty FnMatch
 , fnSig        :: Maybe TT
}
data FnMatch = FnMatch [Pattern] TT
data LetRecT = Let | Rec | LetOrRec

data TTName
 = VLocal  IName
 | VBind   IName | VExtern IName -- TODO rm both since don't understand scopes
 | VToResolve QName -- scope (let-bind / record) found in

data LensOp a = LensGet | LensSet a | LensOver a deriving Show
data DoStmt  = Sequence TT | Bind IName TT -- | Let
data TT -- Type | Term; Parser Expressions (types and terms are syntactically equivalent)
 = Var !TTName
 | Lin QName -- modName used to differentiate dups

 | WildCard           -- "_" implicit lambda argument
 | Question           -- "?" ask to infer
 | Foreign   HName TT -- no definition, and we have to trust the user given type
 | ForeignVA HName TT -- var-args for C externs

 -- lambda-calculus
 | Abs FnDef
 | App TT [TT] -- mixfixless Juxt (used for "case x of .." => "x > \case ")
 | Juxt SourceOffset [TT] -- may contain mixfixes to resolve
 | DoStmts [DoStmt] -- '\n' stands for '*>' , 'pat <- x' stands for '>>= \pat ->'

 -- tt primitives (sum , product , list)
 | Cons   [(FName , TT)] -- can be used to type itself
 | TTLens SourceOffset TT [FName] (LensOp TT)
 | Label  LName [TT]
 | Match  [(LName , FreeVars , [Pattern] , TT)] (Maybe TT)
 | List   [TT]

 -- term primitives
 | Lit      Literal
 | LitArray [Literal]

 -- type primitives
 | TyListOf TT
 | Gadt [(LName , [TT] , Maybe TT)] -- Parameters and constructor signature (return type may be a subtype of the Gadt)

-- patterns represent arguments of abstractions
-- (a b c :: T) introduces implicit pi-bound arguments of type T. note. (a : _) == (a :: _) -> A
data PiBound = PiBound [IName] TT
data Pattern
 = PArg   IName -- introduce VLocal arguments
 | PPi    PiBound
 | PTyped IName TT
 | PComp  IName CompositePattern
 | PGuard Pattern [Pattern] -- case .. of { pat | b <- pat0 , c <- pat1 .. }

data CompositePattern -- the pattern is INamed then split into components (As pats use this IName)
 = PLabel LName [Pattern]
 | PCons  [(FName , Pattern)]
 | PTuple [Pattern]
 | PWildCard
 | PLit   Literal

data ParseState = ParseState {
   _indent      :: Pos    -- start of line indentation (need to save it for subparsers)
 , _piBound     :: [[PiBound]]

 , _moduleWIP   :: Module -- result
}
makeLenses ''ParseState
makeLenses ''ParseDetails
makeLenses ''Module

showL ind = Prelude.concatMap $ (('\n' : ind) <>) . show
prettyModule m = show (m^.moduleName) <> " {\n"
    <> "imports: " <> showL "  " (m^.imports)  <> "\n"
    <> "binds:   " <> showL "  " (m^.bindings) <> "\n"
    <> show (m^.parseDetails) <> "\n}"
prettyParseDetails p = Prelude.concatMap ("\n  " <>)
    [ "binds:  "   <> show (p^.hNameBinds)
    , "args:   "   <> show (p^.hNameArgs)
    , "extern: "   <> show (p^.hNamesNoScope)
    , "fields: "   <> show (p^.fields)
    , "labels: "   <> show (p^.labels)
    , "newlines: " <> show (p^.newLines)
    ]
prettyTTName :: TTName -> Text = \case
    VBind x   -> "π" <> show x
    VLocal  x -> "λ" <> show x
    VExtern x -> "?" <> show x

--deriving instance Show Module
deriving instance Show ParseDetails
deriving instance Show FnDef
--deriving instance Show TopBind
deriving instance Show TTName
deriving instance Show FnMatch
deriving instance Show TT
deriving instance Show DoStmt
deriving instance Show CompositePattern
deriving instance Show PiBound
deriving instance Show Pattern
deriving instance Show LetRecT
