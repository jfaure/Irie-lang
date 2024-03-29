{-# Language TemplateHaskell #-}
module Externs where
import Builtins ( primBinds , primMap , readPrimExtern)
import CoreSyn
import ShowCore()
import CoreUtils(tHeadToTy)
import qualified Data.Vector as V
import Text.Megaparsec (ParseErrorBundle)
import qualified ParseSyntax as P
import Errors
import MixfixSyn
import Control.Lens
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.Binary as DB
import Data.List (partition)
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

-- IName -> ExternVar, for all parsed INames
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
primJM :: JudgedModule
primJM = V.unzip primBinds & \(primHNames , _prims) ->
  JudgedModule 0 "Builtins" primHNames (complement 0) 0 mempty mempty mempty
  -- prim labels are direct bindings
  -- TODO atm this is just a placeholder and prims are looked up differently

builtinRegistry = let
  _timeBuiltins = UTCTime (ModifiedJulianDay 0) (getTime_resolution)
  lBuiltins = LoadedMod 0 0 (JudgeOK 0 primJM)
  in Registry (M.singleton "Builtins" 0) (IM.singleton 0 <$> primMap) mempty (V.singleton lBuiltins)

readQName :: V.Vector LoadedMod -> VQBindIndex -> Maybe Expr
readQName curMods (VQBindIndex q) = let
  modNm = modName q ; iNm = unQName q
  readJudgedBind :: JudgedModule -> IName -> Expr
  readJudgedBind m iNm = snd (m.moduleTT V.! iNm) & bindToExpr
  in case curMods V.! modNm & \(LoadedMod _ _ m) -> m of
--JudgeOK _ jm | testBit jm.labelINames iNm -- vv don't like this, Also Not an IName !
--  then mkQName modNm iNm & \qNameL -> Core (Label qNameL [])
--    (tHeadToTy $ THTyCon $ THSumTy $ BSM.singleton (qName2Key qNameL) (TyGround [THTyCon $ THTuple mempty]))
  JudgeOK _ jm -> Just $ readJudgedBind jm iNm -- & \(Core _t ty) -> Core (Var (VQBindIndex (mkQName modNm iNm))) ty
  _ -> Nothing

lookupIName :: V.Vector LoadedMod -> Int -> Int -> Maybe HName
lookupIName = lookupJM jmINames -- labelNames
lookupJM jmProj lms mName iName = case _loadedImport (lms V.! mName) of
  JudgeOK mI jm -> jmProj jm & \v -> if iName < V.length v then Just (v V.! iName)
    else Just ("Bug: QName " <> showRawQName (mkQName mName iName) <> ": IName exceeds module " <> show mI <> "'s length: " <> show (V.length v))
  _ -> Nothing
lookupLabelBitSet lms mName = case _loadedImport (lms V.! mName) of
  JudgeOK _mI jm -> Just jm.labelINames
  _ -> Nothing

lookupBind :: V.Vector LoadedMod -> ModuleIName -> IName -> Maybe Bind
lookupBind lms mName iName = case _loadedImport (lms V.! mName) of
  JudgeOK _mI jm -> moduleTT jm & \v -> Just (snd (v V.! iName))
  _ -> Nothing

lookupBindName :: V.Vector LoadedMod -> ModuleIName -> IName -> Maybe HName
lookupBindName lms mName iName = case _loadedImport (lms V.! mName) of
  JudgeOK _mI jm -> moduleTT jm & \v -> if V.length v < iName then d_ (V.length v , mName , iName) Nothing -- error "what"
    else letIName (fst (v V.! iName)) & \q ->
    if modName q /= mName then _
    else Just $ jmINames jm V.! unQName q
    -- lookupIName lms (modName q) (unQName q)
  _ -> Nothing

findBindIndex :: PureRegistry -> ModuleIName -> Text -> Maybe IName
findBindIndex reg mI hNm = (reg._allNames M.!? hNm) >>= (IM.!? mI) >>= \iName ->
  case reg._loadedModules V.! mI & \(LoadedMod _ _ m) -> m of
    JudgeOK _mI jm -> Just $ iNameToBindName jm.topINames iName
    _ -> Nothing

-- TODO not pretty
checkExternScope :: BitSet -> ModIName -> Externs -> IName -> ExternVar
checkExternScope openMods thisModIName exts extName = case exts.extNames V.! extName of
  Importable qi@(VQBindIndex q)
    | testBit openMods (modName q) || modName q == 0 -> Importable qi
    | True -> NotOpened openMods qi
  Imported modNm e
    | testBit openMods modNm || modNm == 0 -> Imported modNm e
    | True -> NotOpened openMods (VQBindIndex $ mkQName thisModIName extName) -- ? extName here
  ImportLabel q
    | m <- modName q , testBit openMods m || m == 0 || m == thisModIName -> ImportLabel q
  NotInScope x -> NotInScope (show (bitSet2IntList openMods) <> " : " <> x)
  m@(MixfixyVar (Mixfixy maybeBind mfws)) -> let
    isInScope = \case
      QStartPrefix _ q -> testBit openMods (modName q)
      QStartPostfix _ q -> testBit openMods (modName q)
      QMFPart q -> testBit openMods (modName q)
    (inScope , notInScope) = partition isInScope mfws
    qs = notInScope <&> \case { QStartPrefix _ q -> q ; QStartPostfix _ q -> q ; QMFPart q -> q }
    in if null inScope then NotOpenedINames openMods qs else MixfixyVar (Mixfixy maybeBind inScope)
  x -> x

mfw2qmfw modTopINames modNm = let
  -- get topIName from the IName
  findBindName (MixfixDef i ws f) = MixfixDef (iNameToBindName modTopINames i) ws f
  in \case
  StartPrefix  m i -> QStartPrefix  (findBindName m) (mkQName modNm i)
  StartPostfix m i -> QStartPostfix (findBindName m) (mkQName modNm i)
  MFPart         i -> QMFPart                        (mkQName modNm i)

iNameToBindName :: BitSet -> IName -> IName -- BindName
iNameToBindName topINames iNm = popCount (topINames .&. setNBits iNm :: Integer)

-- * For each IName in a module, figure out if matches any loaded names
resolveNames :: PureRegistry -> IName -> P.Module -> V.Vector HName
  -> (M.Map HName (IntMap IName) , M.Map HName (IM.IntMap [QMFWord]) , Externs)
resolveNames reg modIName p iNamesV = let
  pd = p ^. P.parseDetails
  topINames    = pd ^. P.topINames
  labelINames  = pd ^. P.labelINames
  fieldINames  = pd ^. P.fieldINames
  exposedINames = topINames .|. {-labelINames .|.-} fieldINames
  mfResolver = M.unionWith IM.union reg._globalMixfixWords $
    IM.singleton modIName <$> (map (mfw2qmfw topINames modIName) <$> (pd ^. P.hNameMFWords))

  -- Exposed inames map to a bind index; there are more inames than bind indexes
  getTopINames mI = if mI == modIName then Just topINames
    else case reg._loadedModules V.! mI & \(LoadedMod _ _ m) -> m of
    JudgeOK _mI jm -> Just jm.topINames
    _ -> Nothing

  resolver :: M.Map HName (IM.IntMap IName)
  resolver = M.union reg._allNames $
    IM.singleton modIName <$> M.filter (testBit exposedINames) (pd ^. P.hNamesToINames . _3)

  resolveName :: HName -> ExternVar
  resolveName hNm = let
    binds   = IM.toList <$> (resolver   M.!? hNm)
    mfWords = IM.toList <$> (mfResolver M.!? hNm)
    in case (binds , mfWords) of
    (Just [] , _)  -> NotInScope hNm -- this name was deleted from (all) modules
    (Just [(modNm , iNm)] , Nothing) -> if modNm == 0
      then case readPrimExtern iNm of
       Core (Label q []) _ -> ImportLabel q -- TODO pattern-matching on primBinds is not brilliant
       x -> Imported modNm x -- inline builtins
      else -- case if modNm == modIName then Just labelINames else lookupLabelBitSet reg._loadedModules modNm of
--     Just ls | testBit ls iNm -> ImportLabel (mkQName modNm iNm)
--     _ ->
        if modNm == modIName then ForwardRef iNm else case getTopINames modNm of
          Just top -> Importable (VQBindIndex (mkQName modNm (iNameToBindName top iNm)))
          Nothing  -> _
    (_bind , Just mfWords) -> MixfixyVar (Mixfixy Nothing (concatMap snd mfWords))
    (Nothing   , Nothing)  -> NotInScope hNm
    (Just many , _)        -> AmbiguousBinding hNm many

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
