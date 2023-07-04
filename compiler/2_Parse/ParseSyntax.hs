{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS -funbox-strict-fields #-}
module ParseSyntax where
import Prim ( Literal )
import QName ( QName )
import MixfixSyn ( MFWord, MixfixDef, Prec )
import Errors (ScopeError , MixfixError , UnPatError , ScopeWarning)
import Text.Megaparsec.Pos ( Pos , mkPos )
import Control.Lens ( (^.), makeLenses )
import Data.Functor.Foldable.TH (makeBaseFunctor)
import qualified Data.Map.Strict as M ( Map )
import qualified CoreSyn (Expr , Mixfixy)
import qualified Data.Vector as V

type FName        = IName -- record  fields
type LName        = IName -- sumtype labels
type NameMap      = M.Map HName IName
type SourceOffset = Int
data PImport = POpen HName | PImport HName | POpenData IName [IName] deriving Show
getImportFile = \case { POpen h -> Just h ; PImport h -> Just h ; _ -> Nothing }

data Module = Module { -- Contents of a File (Module = Function : _ → Record | Record)
   _moduleName   :: HName   -- fileName
 , _imports      :: [PImport] -- all imports used at any scope
 , _bindings     :: V.Vector FnDef -- TT
 , _parseDetails :: ParseDetails
}

emptyParsedModule h = Module h [] mempty (ParseDetails mempty (0,mempty,mempty) 0 0 0 [] 0 0)

-- sz , rev list of (Int->HNames) and HName->IName. !NameMap may be smaller than the rev-list
--  ; when INames are promoted to topNames, need to spawn a new IName so topBinds bitset works directly
type HNameMap = (Int , [HName] , NameMap)

-- HNames and local scope
data ParseDetails = ParseDetails {
   _hNameMFWords   :: M.Map HName [MFWord] -- keep count to handle overloads (bind & mfword)
 , _hNamesToINames :: HNameMap -- INames (module-local HName equivalents)
 , _topINames      :: BitSet -- the fields of the module record
 , _fieldINames    :: BitSet
 , _labelINames    :: BitSet
 , _newLines       :: [Int]
 , _letBindCount   :: Int

 , _thisBind       :: IName -- so data/gadt can mark themselves open
}
data FnDef = FnDef {
   _fnNm         :: HName -- TODO rm, isos with the fnIName given an IConv
 , _fnIName      :: IName
 , _fnRecType    :: !LetQual
 , _fnMixfixName :: Maybe MixfixDef
 , _fnRhs        :: TT
 , _fnSrc        :: SourceOffset
}

data LetQual = LetIDK | Let | Dep | Rec | Mut deriving (Eq , Show)

data ScopedName
 = VBruijnLevel IName
 | VBruijn  IName
 | VLetBind (IName , Int , Int , Int) -- iName , letnest , letidx , modiname (lifted name)

data LensOp a = LensGet | LensSet a | LensOver a deriving (Show , Functor , Foldable , Traversable)
data DoStmt  = Sequence TT | Bind IName TT -- | Let
data BruijnAbsF tt = BruijnAbsF
 { _nBound      :: Int
 , _bruijnMetas :: BruijnSubs
 , _bruijnLvl   :: Int -- how many args bound above this level
 , _bruijnBody  :: tt
 } deriving (Show , Functor , Foldable , Traversable)
type BruijnAbs = BruijnAbsF TT
type BruijnSubs = [(IName , Int)] -- Extern -> VBruijn -- TODO can just be a straight list to imap
data CaseSplits = CaseSplits TT [(TT , TT)] -- deliberately wrapped so unaffected by solveScopes initial cata
data CaseSplits' = CaseSplits' [(TT , TT)] -- deliberately wrapped so unaffected by solveScopes initial cata
data Block      = Block { open :: Bool , letType :: LetQual , binds :: V.Vector FnDef }
data TT -- Type | Term; Parser Expressions (types and terms are syntactically equivalent)
 = Var !ScopedName
 | VParseIName IName -- all text names are parsed to an IName
 | Lin QName -- modName used to differentiate dups

 | WildCard           -- "_" implicit lambda argument
 | Question           -- "?" ask to infer
 | Foreign   Bool HName TT -- no definition, and we have to trust the user given type. bool is var-args

 -- lambda-calculus
 | BruijnLam BruijnAbs
 | Juxt SourceOffset [TT] -- may contain mixfixes to resolve
 | PiBound [TT] TT -- (a b c : T) ~> introduces pi-bound arguments of type T

 -- tt primitives (sum , product , list)
 | Prod   (V.Vector (FName , TT)) -- can be used to type itself
 | Tuple   [TT] -- Cartesian product
 | TupleIdx FName TT -- clearer than directly TTLens
 | TTLens SourceOffset TT [FName] (LensOp TT)
 | Label  LName [TT] -- parsed labels "@"
 | QLabel QName
 | LabelDecl Int Int -- IName in this module + its let-offset

 | Guards (Maybe TT) [Guard] TT -- ko-branch (if open case above) , guards , rhs
 | GuardArgs [TT] TT -- Spawn fresh args and pattern-match according to [TT]. no KO branch to jump out of fails
 | FnEqns [TT]

 -- These negative-position TTs must be inverted first before solveScopes
 -- The newtypes hide this to allow interleaving UnPattern with solveScopes
 -- Since both Unpattern and solveScopes deal with deBruijn naming, they may need to be run this way
 -- LambdaCase is also complicated by requiring renaming of deBruijn vars
 | CasePat CaseSplits -- unsolved patterns
 | LambdaCase CaseSplits'

-- | MatchB TT (BSM.BitSetMap TT) (Maybe TT) -- solved patterns UnPattern.patternsToCase
 | MatchB TT [(Either (QName , Int) Int , TT)] (Maybe TT) -- solved patterns UnPattern.patternsToCase

 | List   [TT]
 | LetIn Block Int TT
 | ModBinds Block

 -- term primitives
 | Lit      Literal
 | PLitArray {-(Maybe Int)-} [Literal] -- maybe size
 | PArray {-(Maybe Int)-} [TT] -- maybe size
 | LitEq Literal TT

 -- type primitives
 | TyListOf TT
 | Data [(LName , [TT])] -- lifted let start and Parameters
 | Gadt [(LName , TT)]       -- type signature (return type must be a subtype of the Gadt sig)
 | Typed TT TT

 | DoStmts [DoStmt] -- '\n' stands for '*>' , 'pat <- x' stands for '>>= \pat =>'

 -- desugaring , scope solve
 | DesugarPoison UnPatError
 | ScopeWarn  ScopeWarning TT -- Scope
 | ScopePoison ScopeError
 | InlineExpr CoreSyn.Expr

 -- tmp mixfix vars
 | QVar  QName
 | IQVar QName
 | MFExpr SourceOffset CoreSyn.Mixfixy
 | App SourceOffset TT [TT] -- Used by unpattern and solveMixfixes once clear of precedence & mixfixes
 | PExprApp SourceOffset Prec QName [TT]
 | RawExpr TT -- Skip case for anamorphisms
 | VoidExpr
 | MixfixPoison MixfixError

type Pattern = TT
data Guard
 = GuardBool TT    -- tt =? True
 | GuardPat TT TT  -- pat <- tt -- arbitrary scrut

data IndentType = IndentTab | IndentSpace | IndentEither -- files must commit to an indent style
data ParseState = ParseState {
   _indent      :: Pos        -- start of line indentation (need to save it for subparsers)
 , _indentType  :: IndentType -- tab or space indent style must be consistent
 , _moduleWIP   :: Module -- result
}
emptyParseState nm = ParseState (mkPos 1) IndentEither (emptyParsedModule nm)

makeLenses ''ParseState ; makeLenses ''ParseDetails ; makeLenses ''Module ; makeLenses ''FnDef
makeBaseFunctor ''TT

mkBruijnLam (BruijnAbsF 0 _       _    rhs) = rhs
mkBruijnLam (BruijnAbsF n argSubs nest rhs) = BruijnLam (BruijnAbsF n argSubs nest rhs)

showL ind = Prelude.concatMap $ (('\n' : ind) <>) . show
prettyModule m = show (m^.moduleName) <> " {\n"
    <> "imports: " <> showL "  " (m^.imports)  <> "\n"
    <> "binds:   " <> show (m^.bindings) <> "\n"
    <> show (m^.parseDetails) <> "\n}"
prettyParseDetails p = Prelude.concatMap ("\n  " <>)
    [ "names:  "   <> show (p^.hNamesToINames)
--  , "labels: "   <> show (p^.labels)
--  , "newlines: " <> show (p^.newLines)
    ]

deriving instance Show ParseDetails
deriving instance Show FnDef
deriving instance Show ScopedName
deriving instance Show Block
deriving instance Show TT
deriving instance Show Guard
deriving instance Show CaseSplits
deriving instance Show CaseSplits'
deriving instance Show DoStmt
