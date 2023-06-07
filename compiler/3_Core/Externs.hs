{-# Language TemplateHaskell #-}
module Externs where
import Builtins ( primBinds , primMap )
import CoreSyn
import ShowCore()
import CoreUtils(bind2Expr , tHeadToTy)
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
import qualified BitSetMap as BSM

type Deps = BitSet
type Dependents = BitSet

-- TODO ? should all have a ModIName
data Import
-- = ImportName Text
 = NoPath  Text
 | NoParse Text (ParseErrorBundle Text Void)
 | ImportLoop BitSet -- All deps known; but the loop must be handled specially
 | ParseOK Text ModIName P.Module -- P.Module contains the filepath
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
  JudgedModule 0 "Builtins" primHNames (complement 0) 0 mempty -- prim labels are direct bindings

builtinRegistry = let
  _timeBuiltins = UTCTime (ModifiedJulianDay 0) (getTime_resolution)
  lBuiltins = LoadedMod 0 0 (JudgeOK 0 primJM)
  in Registry (M.singleton "Builtins" 0) (IM.singleton 0 <$> primMap) mempty (V.singleton lBuiltins)

--readLabel {-, readField-} :: Externs -> IName -> QName
--readLabel exts l = if l < 0 then mkQName 0 (-1 - l) else exts.importLabels V.! l

--newtype BindName = BindName IName
-- TODO enforce type safety here
iNameToBindName :: BitSet -> IName -> IName -- BindName
iNameToBindName topINames iNm = popCount (topINames .&. setNBits iNm :: Integer)

readQName :: V.Vector LoadedMod -> ModIName -> IName -> Maybe Expr
readQName curMods modNm iNm = case curMods V.! modNm & \(LoadedMod _ _ m) -> m of
  JudgeOK _ jm -> if testBit jm.labelINames iNm                   
    -- vv don't like this
    then mkQName modNm iNm & \qNameL -> Just $ Core (Label qNameL [])
      (tHeadToTy $ THTyCon $ THSumTy $ BSM.singleton (qName2Key qNameL) (TyGround [THTyCon $ THTuple mempty]))
    else Just $ (readJudgedBind jm iNm) & \(Core t ty) -> Core (Var (VQBind (mkQName modNm iNm))) ty
  _ -> Nothing

readJudgedBind :: JudgedModule -> IName -> Expr
readJudgedBind m iNm = snd (m.moduleTT V.! iNameToBindName (topINames m) iNm) & bind2Expr

readPrimExtern :: IName -> Expr
readPrimExtern i = snd (primBinds V.! i)

lookupIName = lookupJM jmINames -- labelNames
lookupJM jmProj lms mName iName = case _loadedImport (lms V.! mName) of
  JudgeOK _mI jm -> jmProj jm & \v -> if iName < V.length v then Just (v V.! iName)
    else Just ("bugged IName resolution:" <> show iName)
  _ -> Nothing
lookupLabelBitSet lms mName = case _loadedImport (lms V.! mName) of
  JudgeOK _mI jm -> Just jm.labelINames
  _ -> Nothing
lookupBindName :: V.Vector LoadedMod -> ModuleIName -> IName -> _
lookupBindName lms mName iName = case _loadedImport (lms V.! mName) of
  JudgeOK _mI jm -> moduleTT jm & \v -> Just (snd $ v V.! iNameToBindName jm.topINames iName)
  _ -> Nothing

-- TODO not pretty
checkExternScope :: BitSet -> ModIName -> Externs -> IName -> ExternVar
checkExternScope openMods thisModIName exts i = case exts.extNames V.! i of
  Importable modNm iNm
    | modNm == thisModIName -> ForwardRef iNm
    | modNm == 0 -> Imported 0 (readPrimExtern iNm) -- TODO don't always expose builtins!
  Imported modNm e
    | testBit openMods modNm || modNm == 0 -> Imported modNm e
    | True -> NotOpened openMods (mkQName thisModIName i)
  ImportLabel q
    | m <- modName q , testBit openMods m || m == 0 || m == thisModIName -> ImportLabel q
  NotInScope x -> NotInScope (show (bitSet2IntList openMods) <> " : " <> x)
  m@MixfixyVar{} -> m -- TODO
  x -> x

mfw2qmfw topINames modNm = \case
  StartPrefix  m i -> QStartPrefix  m (mkQName modNm i)
  StartPostfix m i -> QStartPostfix m (mkQName modNm i)
  MFPart         i -> QMFPart         (mkQName modNm i)

-- * Add bindNames and local labelNames to resolver
-- * Generate Externs vector
resolveNames :: PureRegistry -> IName -> P.Module -> V.Vector HName
  -> (M.Map HName (IntMap IName) , M.Map HName (IM.IntMap [QMFWord]) , Externs)
resolveNames reg modIName p iNamesV = let
  curAllNames = reg._allNames
  curMFWords  = reg._globalMixfixWords
  curMods     = reg._loadedModules
  pd = p ^. P.parseDetails
  mixfixHNames = pd ^. P.hNameMFWords
  topINames    = pd ^. P.topINames
  labelINames  = pd ^. P.labelINames
  fieldINames  = pd ^. P.fieldINames
  exposedINames = topINames .|. labelINames .|. fieldINames
  mfResolver = M.unionWith IM.union curMFWords $ M.unionsWith IM.union $
    zipWith (\modNm map -> IM.singleton modNm <$> map) [modIName..] [map (mfw2qmfw topINames modIName) <$> mixfixHNames]

  resolver :: M.Map HName (IM.IntMap IName) -- HName -> Modules with that hname
  resolver = let
    exposedNames = -- d_ (bitSet2IntList topINames) $ did_ $
      IM.singleton modIName <$> M.filter (testBit exposedINames) (pd ^. P.hNamesToINames . _3)
    in M.union exposedNames curAllNames

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
--   | testBit labelINames iNm -> ImportLabel (mkQName modNm iNm) -- (clearBit iNm labelBit))
--   | testBit iNm labelBit -> ImportLabel (mkQName modNm (clearBit iNm labelBit))
--   | True -> maybe (Importable modNm iNm) (Imported modNm) (readQName curMods modNm iNm)
     | True -> case if modNm == modIName then Just labelINames else lookupLabelBitSet curMods modNm of
       Just ls | testBit ls iNm -> ImportLabel (mkQName modNm iNm)
       _ -> Importable modNm iNm
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
