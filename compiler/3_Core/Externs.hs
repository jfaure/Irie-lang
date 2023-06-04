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
import qualified Data.Binary as DB
import Data.Time

type Deps = BitSet
type Dependents = BitSet

-- TODO ? should all have a ModIName
data Import
-- = ImportName Text
 = NoPath  Text
 | NoParse Text (ParseErrorBundle Text Void)
 | ImportLoop BitSet -- All deps known; but the loop must be handled specially
 | ParseOK ModIName P.Module -- P.Module contains the filepath
 -- perhaps the ana part that reads depths should instantly register modules and collect inames?
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
type LoadedBinds = V.Vector LoadedMod

lookupLabelName = lookupJM labelNames
lookupFieldName = lookupJM jmINames
lookupJM jmProj lms mName iName = case _loadedImport (lms V.! mName) of
  JudgeOK _mI jm -> jmProj jm & \v -> if iName < V.length v then Just (v V.! iName)
    else Just ("bugged IName resolution:" <> show iName)
  _ -> Nothing

type Registry = MVar PureRegistry
data PureRegistry = Registry {
-- 1. A convention for INaming modules at the top-level
-- 2. Track dependency tree (! Modules know their import-list : [HName] , but not their dependents)
-- 3. Efficient bind/type lookup through all loaded modules (HName -> QName)
-- 4. QName lookup: main bind vector , fields , labels
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
  in JudgedModule 0 "Builtins" primLabelHNames primHNames (complement 0) mempty

builtinRegistry = let
  _timeBuiltins = UTCTime (ModifiedJulianDay 0) (getTime_resolution)
  lBuiltins = LoadedMod 0 0 (JudgeOK 0 primJM)
  in Registry (M.singleton "Builtins" 0) (IM.singleton 0 <$> primMap) mempty (V.singleton lBuiltins)

--readLabel {-, readField-} :: Externs -> IName -> QName
--readLabel exts l = if l < 0 then mkQName 0 (-1 - l) else exts.importLabels V.! l

readPrimExtern :: IName -> Expr
readPrimExtern i = snd (primBinds V.! i)

-- TODO not pretty
checkExternScope :: BitSet -> ModIName -> Externs -> IName -> ExternVar
checkExternScope openMods thisModIName exts i = case exts.extNames V.! i of
  Importable modNm iNm
    -- TODO don't always expose builtins!
    | modNm == thisModIName -> ForwardRef iNm
    | modNm == 0 -> Imported 0 (snd (primBinds V.! iNm))
  Imported modNm e
    | testBit openMods modNm || modNm == 0 -> Imported modNm e
    | True -> NotOpened (did_ openMods) (mkQName thisModIName i)
  ImportLabel q
    | m <- modName q , testBit openMods m || m == 0 || m == thisModIName -> ImportLabel q
  NotInScope x -> NotInScope (show (bitSet2IntList openMods) <> " : " <> x)
  m@MixfixyVar{} -> m -- TODO
  x -> x

readQName :: V.Vector LoadedMod -> ModIName -> IName -> Maybe Expr
readQName curMods modNm iNm = case curMods V.! modNm & \(LoadedMod _ _ m) -> m of
  JudgeOK _ jm -> Just $ (readJudgedBind jm iNm) & \(Core _ ty) -> Core (Var (VQBind (mkQName modNm iNm))) ty
  _ -> Nothing

iNameToBindName topINames iNm = popCount (topINames .&. setNBits iNm :: Integer)

readJudgedBind :: JudgedModule -> IName -> Expr
readJudgedBind m iNm = snd (m.moduleTT V.! iNameToBindName (topINames m) iNm) & bind2Expr

mfw2qmfw topINames modNm = \case
  StartPrefix  (MixfixDef m mfw f) i -> QStartPrefix  (MixfixDef (m) mfw f) (mkQName modNm i)
  StartPostfix (MixfixDef m mfw f) i -> QStartPostfix (MixfixDef (m) mfw f) (mkQName modNm i)
  MFPart                           i -> QMFPart                             (mkQName modNm i)

-- * Add bindNames and local labelNames to resolver
-- * Generate Externs vector
resolveNames :: PureRegistry -> IName -> P.Module -> V.Vector HName
  -> (M.Map HName (IntMap IName) , M.Map HName (IM.IntMap [QMFWord]) , Externs)
resolveNames reg modIName p iNamesV = let
  curAllNames = reg._allNames
  curMFWords  = reg._globalMixfixWords
  curMods     = reg._loadedModules
  mixfixHNames = p ^. P.parseDetails . P.hNameMFWords
  topINames = p ^. P.parseDetails . P.topINames
  mfResolver = M.unionWith IM.union curMFWords $ M.unionsWith IM.union $
    zipWith (\modNm map -> IM.singleton modNm <$> map) [modIName..] [map (mfw2qmfw topINames modIName) <$> mixfixHNames]

  -- Note. temporary labelBit allows searching BindNames and labels in 1 Map
  -- In fact labels are almost bindNames in their own right
  resolver :: M.Map HName (IM.IntMap IName) -- HName -> Modules with that hname
  resolver = let
    labelMap = p ^. P.parseDetails . P.labels
    labels = IM.singleton modIName . (`setBit` labelBit) <$> labelMap
    exposedNames = M.filter (testBit (p ^. P.parseDetails . P.topINames)) (p ^. P.parseDetails . P.hNamesToINames)
    in M.unionsWith IM.union [(IM.singleton modIName <$> exposedNames) , curAllNames , labels]

  resolveName :: HName -> ExternVar
  resolveName hNm = let
    binds   = IM.toList <$> (resolver   M.!? hNm)
    mfWords = IM.toList <$> (mfResolver M.!? hNm)
    in case (binds , mfWords) of
    (Just [] , _)  -> NotInScope hNm -- this name was deleted from (all) modules
    -- inline builtins
    (Just [(modNm , iNm)] , Nothing) -> if
     | modNm == 0 -> case snd (primBinds V.! iNm) of
       Core (Label q []) _ -> ImportLabel q -- TODO pattern-matching on primBinds is not brilliant
       x -> Importable modNm iNm -- Imported x
     | testBit iNm labelBit -> ImportLabel (mkQName modNm (clearBit iNm labelBit))
     | True -> maybe (Importable modNm iNm) (Imported modNm) (readQName curMods modNm iNm)
--   | True -> Importable modNm iNm
    (b , Just mfWords) -> let flattenMFMap = concatMap snd in MixfixyVar $ case b of
      Nothing      -> Mixfixy Nothing              (flattenMFMap mfWords)
      Just [(m,i)] -> Mixfixy (Just (mkQName m i)) (flattenMFMap mfWords)
      _ -> error "TODO"
    (Nothing      , Nothing) -> NotInScope hNm
    (Just many , _)          -> AmbiguousBinding hNm many

  in (resolver , mfResolver , Externs (resolveName <$> iNamesV))

showImportCon :: Import -> Text
showImportCon = \case
  NoPath{} -> "NoPath"
  NoParse{} -> "NoParse"
  ImportLoop{} -> "ImportLoop"
  ParseOK{} -> "ParseOK"
  JudgeOK{} -> "JudgeOK"
  NoJudge{} -> "NoJudge"
  IRoot{} -> "IRoot"
  ImportQueued{} -> "ImportQueued"

--deriving instance Generic PureRegistry
deriving instance Generic QMFWord
deriving instance Generic MixfixDef
deriving instance Generic Prec
deriving instance Generic Assoc
deriving instance Generic QName
--instance DB.Binary PureRegistry
instance DB.Binary QMFWord
instance DB.Binary MixfixDef
instance DB.Binary Prec
instance DB.Binary Assoc
instance DB.Binary QName
