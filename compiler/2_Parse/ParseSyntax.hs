{-# LANGUAGE TemplateHaskell , TypeFamilies #-}
{-# OPTIONS -funbox-strict-fields #-}
module ParseSyntax where
import Prim ( Literal )
import QName ( QName )
import MixfixSyn ( MFWord, MixfixDef, Prec )
import Errors (ScopeError)
import Text.Megaparsec.Pos ( Pos , mkPos )
import Control.Lens ( (^.), makeLenses )
import Data.Functor.Foldable.TH (makeBaseFunctor)
import qualified BitSetMap as BSM
import qualified Data.Map.Strict as M ( Map )
import qualified CoreSyn (Expr , Mixfixy)
import qualified Data.Vector as V

type FName        = IName -- record  fields
type LName        = IName -- sumtype labels
type NameMap      = M.Map HName IName
type SourceOffset = Int

data Module = Module { -- Contents of a File (Module = Function : _ → Record | Record)
   _moduleName   :: HName   -- fileName
 , _imports      :: [HName] -- all imports used at any scope
 , _bindings     :: TT
 , _parseDetails :: ParseDetails
}
-- To allow the repl to continue
emptyParsedModule h = Module h [] Question (ParseDetails (0 , mempty) mempty mempty mempty [])

-- HNames and local scope
data ParseDetails = ParseDetails {
   _hNameMFWords  :: (Int , M.Map HName [MFWord]) -- keep count to handle overloads (bind & mfword)
 , _hNameBinds    :: M.Map HName IName -- top-level and let-bound assignments TODO list is sufficient here
 , _hNamesNoScope :: NameMap -- INames (module-local HName equivalents)
 , _labels        :: NameMap
 , _newLines      :: [Int]
}
data FnDef = FnDef {
   _fnNm         :: HName
 , _fnIName      :: IName
 , _fnRecType    :: !LetRecT
 , _fnMixfixName :: Maybe MixfixDef -- rm (mixfixes are aliases)
 , _fnRhs        :: TT
 , _fnSig        :: Maybe TT
}

-- single argument match
data FnMatch = FnMatch TT TT -- TODO rm
data LetRecT = LetIDK | Let | Dep | Rec | Mut deriving (Eq , Show) -- scope of opened records (blocks)

data TTName
 = VBruijnLevel IName
 | VBruijn  IName
 | VExtern  IName
 | VQBind   QName
 | VLetBind QName -- let-block nesting depth and IName

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
data CaseSplits' = CaseSplits' [(TT , TT)] -- deliberately wrapped so unaffected by solveScopes initial cata
data Block      = Block { open :: Bool , letType :: LetRecT , binds :: V.Vector FnDef }
data TT -- Type | Term; Parser Expressions (types and terms are syntactically equivalent)
 = Var !TTName
 | Lin QName -- modName used to differentiate dups

 | WildCard           -- "_" implicit lambda argument
 | Question           -- "?" ask to infer
 | Foreign   Bool HName TT -- no definition, and we have to trust the user given type. bool is var-args

 -- lambda-calculus
 | BruijnLam BruijnAbs
 | App TT [TT] -- Used by unpattern and solveMixfixes once clear of precedence & mixfixes
 | AppExt IName [TT] -- possibly a label application
 | Juxt SourceOffset [TT] -- may contain mixfixes to resolve
 | PiBound [TT] TT -- (a b c : T) introduces pi-bound arguments of type T

 -- tt primitives (sum , product , list)
-- | Prod   [(FName , TT)] -- can be used to type itself
 | Tuple   [TT] -- Cartesian product
 | ArgProd TT -- argument; used only by UnPattern within case expressions
 | TTLens SourceOffset TT [FName] (LensOp TT)
 | Label  LName [TT]

 | PatternGuards [TT]

 -- These negative-position TTs must be inverted first before solveScopes
 -- The newtypes hide this to allow interleaving UnPattern with solveScopes
 -- Since both Unpattern and solveScopes deal with deBruijn naming, they may need to be run this way
 -- LambdaCase is also complicated by requiring renaming of deBruijn vars
 | CasePat CaseSplits -- unsolved patterns
 | LamPats FnMatch
 | LambdaCase CaseSplits'

 | MatchB TT (BSM.BitSetMap TT) (Maybe TT) -- solved patterns UnPattern.patternsToCase

 | List   [TT]
 | LetIn Block (Maybe TT)

 -- term primitives
 | Lit      Literal
 | LitArray [Literal]
 | LitEq Literal TT

 -- type primitives
 | TyListOf TT
 | Gadt [(LName , [TT] , Maybe TT)] -- Parameters and constructor signature (return type may be a subtype of the Gadt)

 | DoStmts [DoStmt] -- '\n' stands for '*>' , 'pat <- x' stands for '>>= \pat =>'

 -- desugaring
 | DesugarPoison Text  -- UnPattern errors
 | ScopeWarn  Text TT -- Scope
 | ScopePoison ScopeError
 | InlineExpr CoreSyn.Expr

 -- tmp mixfix vars
 | QVar QName
 | MFExpr CoreSyn.Mixfixy
 | PExprApp Prec QName [TT]
 | RawExpr TT -- Skip case for anamorphisms
 | VoidExpr
 | MixfixPoison Text

type Pattern = TT

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
mkBruijnLam (BruijnAbsF n argSubs nest rhs) = case rhs of
--BruijnLam (BruijnAbsF n2 argSubs2 nest2 rhs2) -> d_ rhs $
--  if nest /= 0 || nest2 /= 0 then error "what is nest"
--  else mkBruijnLam (BruijnAbsF (n + n2) ((argSubs <&> \(i,b) -> (i , b + n2)) ++ argSubs2) 0 rhs2)
  _ -> BruijnLam (BruijnAbsF n argSubs nest rhs)

showL ind = Prelude.concatMap $ (('\n' : ind) <>) . show
prettyModule m = show (m^.moduleName) <> " {\n"
    <> "imports: " <> showL "  " (m^.imports)  <> "\n"
    <> "binds:   " <> show (m^.bindings) <> "\n"
    <> show (m^.parseDetails) <> "\n}"
prettyParseDetails p = Prelude.concatMap ("\n  " <>)
    [ "names:  "   <> show (p^.hNamesNoScope)
    , "labels: "   <> show (p^.labels)
--  , "newlines: " <> show (p^.newLines)
    ]

deriving instance Show ParseDetails
deriving instance Show FnDef
deriving instance Show FnMatch
deriving instance Show TTName
deriving instance Show Block
deriving instance Show TT
deriving instance Show CaseSplits
deriving instance Show CaseSplits'
deriving instance Show DoStmt
