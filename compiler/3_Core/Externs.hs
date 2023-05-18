{-# Language TemplateHaskell #-}
module Externs where
import Builtins ( primBinds , primMap , primLabelHNames )
import CoreSyn
import ShowCore()
import CoreUtils(bind2Expr)
import qualified Data.Vector as V
import Text.Megaparsec (ParseErrorBundle)
import qualified ParseSyntax as P
import Errors
import MixfixSyn
import Control.Lens
import qualified Data.IntMap as IM
import qualified Data.Map as M
import Data.Time

type Deps = BitSet
type Dependents = BitSet

-- TODO ? should all have a ModIName
data Import
 = ImportName Text
 | NoPath  Text
 | NoParse Text (ParseErrorBundle Text Void)
 | ImportLoop BitSet -- All deps known; but the loop must be handled specially
 | ParseOK ModIName P.Module -- P.Module contains the filepath
 | JudgeOK ModIName JudgedModule
 | NoJudge ModIName Errors
-- | Cached  ModIName FilePath
 | IRoot -- For compiling multiple files on cmdline without a root module
 | ImportQueued (MVar ())

data LoadedMod = LoadedMod
 { _deps :: Deps
 , _dependents :: Dependents
 , _loadedImport :: Import
 }; -- makeLenses ''LoadedMod

newtype Externs = Externs { extNames :: V.Vector ExternVar } deriving Show

type Registry = MVar PureRegistry
data PureRegistry = Registry {
-- 1. A convention for INaming modules at the top-level
-- 2. Track dependency tree (! Modules know their import-list : [HName] , but not their dependents)
-- 3. Efficient bind/type lookup through all loaded modules
-- 4. QName lookup (QName -> HName): main bind vector , fields , labels
-- 5. Tracks file freshness and read/writes to cache
-- 6. Module edits (Add specialisations , incremental compilation)
   _modNames          :: M.Map HName IName
 , _allNames          :: M.Map HName (IM.IntMap IName) -- HName -> ModIName -> IName
 , _globalMixfixWords :: M.Map HName (IM.IntMap [QMFWord])
 , _loadedModules     :: V.Vector LoadedMod
  -- ! refreshing cache / rewriting old modules may mess up dependents
}; makeLenses ''PureRegistry

-- Note. We read builtins directly , this just occupies Module Name 0
primJM = V.unzip primBinds & \(primHNames , _prims) ->
  let _letBinds = LetBlock mempty -- (\x -> _ :: _) <$> prims
  in JudgedModule 0 "Builtins" primHNames primLabelHNames mempty (Core Question tyBot)

builtinRegistry = let
  _timeBuiltins = UTCTime (ModifiedJulianDay 0) (getTime_resolution)
  lBuiltins = LoadedMod 0 0 (JudgeOK 0 primJM)
  in Registry (M.singleton "Builtins" 0) (IM.singleton 0 <$> primMap) mempty (V.singleton lBuiltins)

--readLabel {-, readField-} :: Externs -> IName -> QName
--readLabel exts l = if l < 0 then mkQName 0 (-1 - l) else exts.importLabels V.! l

readPrimExtern :: IName -> Expr
readPrimExtern i = snd (primBinds V.! i)

-- TODO rm this
readParseExtern :: BitSet -> ModIName -> Externs -> IName -> ExternVar
readParseExtern openMods thisModIName exts i = case exts.extNames V.! i of
  Importable modNm iNm -> if
    | modNm == thisModIName -> ForwardRef iNm
    | modNm == 0 -> Imported (snd (primBinds V.! iNm))
    | True -> NotOpened (show modNm <> "." <> show iNm) ("")
    -- readQParseExtern openMods thisModIName exts modNm iNm
  x -> x

-- exported functions to resolve ParseSyn.VExterns
--readQParseExtern :: BitSet -> Int -> Externs -> Int -> IName -> CoreSyn.ExternVar
--readQParseExtern openMods thisModIName (exts :: Externs) modNm iNm = if
--  | modNm == thisModIName    -> ForwardRef iNm -- solveScopes can handle this
-- | openMods `testBit` modNm -> Imported $ case snd (exts.extBinds V.! modNm V.! iNm) of
--   e@(Core f t) -> case f of -- inline trivial things
--     Lit{}   -> e
--     Instr{} -> e
--     Var{}   -> e -- var indirection (TODO continue maybe inlining?)
--     _ -> e
--     _ -> Core (Var $ VQBind (mkQName modNm iNm)) t
--  | otherwise -> NotOpened (show modNm {-exts.eModNamesV V.! modNm-}) (fst (exts.extBinds V.! modNm V.! iNm))

readQName :: V.Vector LoadedMod -> ModIName -> IName -> ExternVar
readQName curMods modNm iNm = case curMods V.! modNm & \(LoadedMod _ _ m) -> m of
  JudgeOK _ jm -> Imported (readJudgedBind jm iNm)
  _ -> Importable modNm iNm

readJudgedBind :: JudgedModule -> IName -> Expr
readJudgedBind m iNm = case m.moduleTT of
  Core (LetBlock binds) _ -> snd (binds V.! iNm) & bind2Expr
  _ -> _

showImportCon :: Import -> Text
showImportCon = \case
  ImportName{} -> "ImportName"
  NoPath{} -> "NoPath"
  NoParse{} -> "NoParse"
  ImportLoop{} -> "ImportLoop"
  ParseOK{} -> "ParseOK"
  JudgeOK{} -> "JudgeOK"
  NoJudge{} -> "NoJudge"
  IRoot{} -> "IRoot"
  ImportQueued{} -> "ImportQueued"

--deriving instance Generic LoadedMod
--deriving instance Generic Registry
--instance DB.Binary LoadedMod
--instance DB.Binary Registry
