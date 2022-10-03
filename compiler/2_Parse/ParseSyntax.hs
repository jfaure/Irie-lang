{-# LANGUAGE TemplateHaskell , TypeFamilies #-}
{-# OPTIONS  -funbox-strict-fields #-}
module ParseSyntax where
import Prim ( Literal )
import QName ( QName )
import MixfixSyn ( MFWord, MixfixDef, ModIName )
import Control.Lens ( (^.), makeLenses )
import Text.Megaparsec.Pos ( Pos )
import qualified Data.Map.Strict as M ( Map )
import qualified BitSetMap as BSM
import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.Void
import Errors (ScopeError)
import qualified CoreSyn (Expr , Mixfixy)
import MixfixSyn

type FName        = IName -- record  fields
type LName        = IName -- sumtype labels
type FreeVar      = IName -- non-local argument
type FreeVars     = BitSet
type NameMap      = M.Map HName IName
type SourceOffset = Int

data Module = Module { -- Contents of a File (Module = Function : _ → Record | Record)
   _moduleName   ∷ HName -- fileName
-- , _modFunctor   ∷ [Pattern]
-- , _modSig       ∷ Maybe TT
 , _imports      ∷ [HName] -- all imports used at any scope
 , _bindings     ∷ [FnDef] -- hNameBinds (! these are listed in reverse)

 , _parseDetails ∷ ParseDetails
}
-- To allow the repl to continue
emptyParsedModule h = Module h [] [] (ParseDetails (0 , mempty) mempty mempty mempty mempty [])

-- args and signature for the module (return type must be a record)
-- data FunctorModule = FunctorModule [Pattern] (Maybe TT) SourceOffset

-- HNames and local scope
data ParseDetails = ParseDetails {
   _hNameMFWords   ∷ (Int , M.Map HName [MFWord]) -- keep count to handle overloads (bind & mfword)
 , _hNameBinds     :: M.Map HName IName -- top-level and let-bound assignments
 , _hNamesNoScope  ∷ NameMap
 , _fields         ∷ NameMap
 , _labels         ∷ NameMap
 , _newLines       ∷ [Int]
}
data FnDef = FnDef {
   fnNm         ∷ HName
 , fnRecType    ∷ !LetRecT        -- or mutual
 , fnMixfixName ∷ Maybe MixfixDef -- rm (mixfixes are aliases)
 , fnMatches    ∷ TT -- BruijnAbs -- NonEmpty FnMatch
 , fnSig        ∷ Maybe TT
}

data FnMatch = FnMatch [TT] TT
data LetRecT = Let | Rec | LetOrRec deriving Eq

data TTName
 = VBruijn IName
 | VExtern IName
 | VQBind  QName -- not ideal here

data LensOp a = LensGet | LensSet a | LensOver a deriving (Show , Functor , Foldable , Traversable)
data DoStmt  = Sequence TT | Bind IName TT -- | Let
data BruijnAbsF tt = BruijnAbsF
 { _nBound      :: Int
 , _bruijnMetas :: BruijnSubs
 , _bruijnNest  :: Int -- how many args bound above this level
 , _bruijnBody  :: tt
 } deriving (Show , Functor , Foldable , Traversable)
type BruijnAbs = BruijnAbsF TT
type BruijnSubs = [(IName , Int)] -- Extern -> VBruijn -- TODO can just be a straight list to imap
data CaseSplits = CaseSplits TT [(TT , TT)] -- deliberately wrapped so unaffected by solveScopes initial cata
data TT -- Type | Term; Parser Expressions (types and terms are syntactically equivalent)
 = Var !TTName
 | Lin QName -- modName used to differentiate dups

 | WildCard           -- "_" implicit lambda argument
 | Question           -- "?" ask to infer
 | Foreign   HName TT -- no definition, and we have to trust the user given type
 | ForeignVA HName TT -- var-args for C externs

 -- lambda-calculus
 | BruijnLam BruijnAbs
 | App TT [TT] -- Used by unpattern and solveMixfixes once clear of precedence & mixfixes
 | Juxt SourceOffset [TT] -- may contain mixfixes to resolve
 | PiBound [TT] TT -- (a b c : T) introduces pi-bound arguments of type T

 -- tt primitives (sum , product , list)
 | Prod   [(FName , TT)] -- can be used to type itself
 | ArgProd [TT] -- packed arguments; used only by UnPattern within case expressions
 | Tuple   [TT]
 | TTLens SourceOffset TT [FName] (LensOp TT)
 | Label  LName [TT]

 | PatternGuards [TT] -- Only parsed in pattern position
 | CasePat CaseSplits -- unsolved patterns
 | MatchB TT (BSM.BitSetMap TT) (Maybe TT)

 | List   [TT]
-- | LetBinds [(IName , BruijnAbs)] TT -- marker for let-block / opened Module
 | LetBinds [(IName , TT)] TT -- marker for let-block / opened Module

 -- term primitives
 | Lit      Literal
 | LitArray [Literal]
 | LitEq Literal TT

 -- type primitives
 | TyListOf TT
 | Gadt [(LName , [TT] , Maybe TT)] -- Parameters and constructor signature (return type may be a subtype of the Gadt)

 | DoStmts [DoStmt] -- '\n' stands for '*>' , 'pat ← x' stands for '≫= \pat ⇒'

 -- desugaring
 | DesugarPoison Text  -- UnPattern errors
 | ScopeWarn  Text TT -- Scope
 | ScopePoison ScopeError
 | InlineExpr CoreSyn.Expr

 -- tmp mixfix vars
 | QVar QName
 | MFExpr CoreSyn.Mixfixy
 | PExprApp Prec QName [TT]
 | RawExpr TT
 | VoidExpr
 | MixfixPoison Text

type Pattern = TT

data IndentType = IndentTab | IndentSpace | IndentEither -- files must commit to an indent style
data ParseState = ParseState {
   _indent      ∷ Pos    -- start of line indentation (need to save it for subparsers)
 , _indentType  ∷ IndentType

 , _moduleWIP   ∷ Module -- result
}
makeLenses ''ParseState
makeLenses ''ParseDetails
makeLenses ''Module
makeBaseFunctor ''TT

mkBruijnLam (BruijnAbsF 0 _       _    rhs) = rhs
mkBruijnLam (BruijnAbsF n argSubs nest rhs) = BruijnLam (BruijnAbsF n argSubs nest rhs)

showL ind = Prelude.concatMap $ (('\n' : ind) <>) . show
prettyModule m = show (m^.moduleName) <> " {\n"
    <> "imports: " <> showL "  " (m^.imports)  <> "\n"
    <> "binds:   " <> showL "  " (m^.bindings) <> "\n"
    <> show (m^.parseDetails) <> "\n}"
prettyParseDetails p = Prelude.concatMap ("\n  " <>)
    [ "names:  "   <> show (p^.hNamesNoScope)
    , "fields: "   <> show (p^.fields)
    , "labels: "   <> show (p^.labels)
    , "newlines: " <> show (p^.newLines)
    ]

deriving instance Show ParseDetails
deriving instance Show FnDef
deriving instance Show TTName
deriving instance Show FnMatch
deriving instance Show TT
deriving instance Show CaseSplits
deriving instance Show DoStmt
deriving instance Show LetRecT
