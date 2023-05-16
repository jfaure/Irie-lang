{-# Language TemplateHaskell #-}
module Registry where
import CmdLine
import CoreSyn
import Builtins
import qualified ParseSyntax as P
import Parser (parseModule)
import CoreBinary()
import PrettyCore
import Infer(judgeModule)
import qualified BetaEnv(simpleExpr)
import Text.Megaparsec (errorBundlePretty)
import ModulePaths
import Errors
import MixfixSyn
import Externs
import qualified BitSetMap as BSM
import Data.Time
import Data.Functor.Base
import qualified Data.Text as T
import qualified Data.Text.IO as T.IO
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TL.IO
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Map.Strict as M
import qualified Data.IntMap as IM
import qualified Data.Binary as DB
import Control.Lens
import Control.Concurrent.Async
import System.Directory ( createDirectoryIfMissing, doesFileExist, getModificationTime, removeFile )
--import System.FileLock
--import qualified System.IO as SIO -- (hClose , openTempFile)

searchPath = ["./" , "ii/"]
objPath    = ["./"]
objDir     = ".irie-obj/"
g_noCache  = True
doFuse     = True
cacheVersion = 0
registryFName = ""
doParallel = False

-- ## Deps: build dep-tree > parallel judge dep-tree & Write ↓↑deps to registry
-- ## IConv: Must use registry ModINames (else β for trans imports too complicated)
--   => Modules depend on Registry modINames and Registry becomes inflexible
--     * Merge 2 registries requires renaming QNames in all modules in one of them
--     * All deps must be ModINamed before processing (Cannot seal dep-tree)
--     * INames (iconv) vs BindNames (module bindVector elements)
-- ## RegMap : Global bind-lookup (HName -> IMap INames)
--   * If mod IConv changes; need to also update regMap (use oldHNames to find them)

-- TODO simplifyModule
-- TODO only print stuff if requested
-- TODO search(fuzzy?) Registry (hackage edit-distance)
-- TODO print dep-tree / print Tocompile tree
-- TODO Append module (for repl) & suspended parse & parse Expr
-- TODO cache (lockfile) , CachedModule = Import
-- TODO Import loops: Need to concat parsed modules => _mutMod { open m2Def ; open m2Def }
--   How to merge IConvs ?!
-- TODO mergeRegistries
-- TODO ImportedSig: BitSet of imported binds from each module (depends on scope)

-- Note. We read builtins directly , this just occupies Module Name 0
primJM = V.unzip primBinds & \(primHNames , _prims) ->
  let _letBinds = LetBlock mempty -- (\x -> _ :: _) <$> prims
  in JudgedModule 0 "Builtins" primHNames primLabelHNames (Core Question tyBot)

type Registry = MVar PureRegistry
data PureRegistry = Registry {
-- 1. A convention for INaming modules at the top-level
-- 2. Track dependency tree (! Modules know their import-list : [HName] , but not their dependents)
-- 3. Efficient bind/type lookup through all loaded modules
-- 4. QName lookup:
--   * iNames/labelNames: QName -> HName (fields / Labels)
--   * allNames:          QName -> HName (module main bind vector)
-- 5. Tracks file freshness and read/writes to cache
-- 6. Module edits (Add specialisations , incremental compilation)
   _modNames          :: M.Map HName IName
 , _allNames          :: M.Map HName (IM.IntMap IName) -- HName -> ModIName -> IName
 , _globalMixfixWords :: M.Map HName (IM.IntMap [QMFWord])
 , _loadedModules     :: V.Vector LoadedMod
  -- ! refreshing cache / rewriting old modules may mess up dependents
}; makeLenses ''PureRegistry
--deriving instance Generic LoadedMod
--deriving instance Generic Registry
--instance DB.Binary LoadedMod
--instance DB.Binary Registry

lookupIName    = lookupJM labelNames
lookupBindName = lookupJM bindNames
lookupJM jmProj lms mName iName = case _loadedImport (lms V.! mName) of
  JudgeOK _mI jm -> Just (jmProj jm V.! iName)
  _ -> Nothing

builtinRegistry = let
  _timeBuiltins = UTCTime (ModifiedJulianDay 0) (getTime_resolution)
  lBuiltins = LoadedMod 0 0 (JudgeOK 0 primJM)
  in Registry (M.singleton "Builtins" 0) (IM.singleton 0 <$> primMap) mempty (V.singleton lBuiltins)

-- useCache
initRegistry False  = newMVar builtinRegistry
initRegistry True = doesFileExist registryFName >>= \case
  True  -> _ -- DB.decodeFile registryFName
  False -> newMVar builtinRegistry

getLoadedModule :: Registry -> ModIName -> IO LoadedMod
getLoadedModule reg modIName = readMVar reg <&> \r -> r._loadedModules V.! modIName

-- Left New module ||| Right already registered module
registerModule :: Registry -> HName -> IO (Either ModIName ModIName)
registerModule reg' fPath = takeMVar reg' >>= \reg -> let iM = M.size reg._modNames
  in case M.insertLookupWithKey (\_k _new old -> old) fPath iM reg._modNames of
    (Just iM , _mp) -> Left iM  <$ putMVar reg' reg -- cached module IName found (it may still need to be recompiled)
    (Nothing , mp)  -> Right iM <$ putMVar reg'
      (reg & modNames .~ mp & loadedModules %~ (`V.snoc` (LoadedMod 0 0 (ImportName fPath))))

data InCompile = InText Text | InFilePath (Either FilePath FilePath)

-- Compilation Hylo on Deptree:
-- 1. anaM => check module loops, assign registry MINames , passdown dependents
-- 2. cata => register all modules + deps/dependents + parallel judge modules
compileFiles :: CmdLine -> Registry -> [FilePath] -> IO ()
compileFiles cmdLine reg = let
  compFile f = findModule searchPath (toS f) >>= \fPath -> join $
    hyloM (judgeTree cmdLine reg) (readDeps reg) (0 , InFilePath fPath)
  in mapConcurrently_ compFile

-- Somewhat a hack (?)
textModName = "<text>" :: Text -- module Name for text strings; This will be overwritten each time

compileText :: CmdLine -> Registry -> Text -> IO (Maybe Import)
compileText cmdLine reg progText = do
  void $ join (hyloM (judgeTree cmdLine reg) (readDeps reg) (0 , InText progText))
  modIName <- readMVar reg <&> (M.! textModName) . _modNames
  getLoadedModule reg modIName <&> Just . _loadedImport

type MISeed = (Dependents , InCompile)
readDeps :: Registry -> MISeed -> IO (TreeF (Dependents , Import) MISeed)
readDeps reg (ds , input) = let
  pathKO fPath = pure (NodeF (ds , NoPath (T.pack fPath)) [])
  -- assign a regIName to new modules & check loops
  pathOK :: FilePath -> IO (TreeF (Dependents , Import) MISeed)
  pathOK fPath = let
    newModule iM   = parseFileImports iM fPath
    knownModule iM = if ds `testBit` iM
      then pure $ NodeF (ds , ImportLoop ds) []
      else getLoadedModule reg iM >>= \loaded ->
        case True of -- is the cached module fresh?
          True  -> pure $ NodeF (ds , loaded._loadedImport) [] -- []: deps already registered
          False -> parseFileImports iM fPath
    in registerModule reg (T.pack fPath) >>= knownModule ||| newModule

  parseFileImports :: IName -> FilePath -> IO (TreeF (Dependents , Import) MISeed)
  parseFileImports iM fPath = T.IO.readFile fPath >>= inText iM fPath

  inText :: IName -> FilePath -> Text -> IO (TreeF (Dependents , Import) MISeed)
  inText iM fPath txt = case parseModule fPath txt of
    Left parseKO -> pure (NodeF (ds , NoParse (T.pack fPath) parseKO) [])
    Right p -> ((fmap InFilePath . findModule searchPath . toS) `mapM` (p ^. P.imports))
      <&> \imports -> NodeF (ds , ParseOK iM p) ((setBit ds iM , ) <$> imports)
  in case input of
  InText txt -> registerModule reg textModName
    >>= \iM -> inText ((identity ||| identity) iM) (T.unpack textModName) txt
  InFilePath iPath -> (pathKO ||| pathOK) iPath

-- TODO
registerDeps reg mI deps dependents = pure () -- takeMVar reg >>= \r -> r & loadedMods %~

-- Add bindNames to allBinds!
registerJudgedMod :: Registry -> ModIName -> Either Errors (_ , _ , JudgedModule) -> IO ()
registerJudgedMod reg mI = let
  addJM (resolver , mfResolver , jm) = takeMVar reg >>= \r -> putMVar reg (
    r & loadedModules %~ V.modify (\v -> MV.modify v (\(LoadedMod deps dents _m) -> LoadedMod deps dents (JudgeOK mI jm)) mI)
      & Registry.allNames .~ resolver
      & Registry.globalMixfixWords .~ mfResolver
    )
  in const (pure ()) ||| addJM

-- cata DepTree => parallel judge modules , register all modules and deps/dependents
judgeTree :: CmdLine -> Registry -> TreeF (Dependents , Import) (IO Deps) -> IO Deps
judgeTree cmdLine reg (NodeF (dependents , mod) m_depL) = mapConcurrently identity m_depL
  >>= \depL -> let deps = foldr (.|.) 0 depL in case mod of
  NoPath fName -> deps <$ putStrLn ("Not found: \"" <> fName <> "\"")
  NoParse _fName parseError -> deps <$ putStrLn (errorBundlePretty parseError)
  JudgeOK mI jm -> setBit dependents mI <$ registerDeps reg mI deps dependents
  ParseOK mI pm -> readMVar reg >>= \reg' -> deps <$ -- setBit dependents mI
    let (resolver , mfResolver , exts) = resolveNames reg' mI pm
        getBindSrc = readMVar reg <&> \r -> -- Need to read this after registering current module
          BindSource (lookupIName r._loadedModules) (lookupBindName r._loadedModules)
    in case judge deps reg' exts mI pm of
      Left (errs , jm) -> let
        in registerJudgedMod reg mI (Left errs)
        *> getBindSrc >>= \bindSrc ->
        putErrors stdout Nothing bindSrc errs
        *> putStrLn @Text ("KO \"" <> pm ^. P.moduleName <> "\"(" <> show mI <> ")")
      Right jm -> registerJudgedMod reg mI (Right (resolver , mfResolver , jm))
        *> when ("core" `elem` printPass cmdLine)
        (getBindSrc >>= \bindSrc ->
        putJudgedModule cmdLine (Just bindSrc) jm
        *> putStrLn @Text ("OK \"" <> pm ^. P.moduleName <> "\"(" <> show mI <> ")"))
  ImportLoop ms -> error $ "import loop: " <> show (bitSet2IntList ms)
  NoJudge _mI _jm -> pure deps
  IRoot -> error "root"
  ImportName _ -> error "importName"

putJudgedModule cmdLine bindSrc jm = let
  outHandle = stdout
  putBind = not $ "types" `elem` printPass cmdLine 
  renderOpts = ansiRender { bindSource = bindSrc , ansiColor = not (noColor cmdLine) }
  putJM = True -- ("core" `elem` printPass flags || "opt" `elem` printPass flags)
  in when putJM $ TL.IO.hPutStrLn outHandle (prettyJudgedModule putBind renderOpts jm)

-- * Add bindNames and local labelNames to resolver
-- * Generate Externs vector
resolveNames :: PureRegistry -> IName -> P.Module -> (_ , _ , Externs)
resolveNames reg modIName p = let
  curAllNames = reg._allNames
  curMFWords  = reg._globalMixfixWords
  curMods     = reg._loadedModules
  mixfixHNames = p ^. P.parseDetails . P.hNameMFWords . _2
  mfResolver = M.unionWith IM.union curMFWords $ M.unionsWith IM.union $
    zipWith (\modNm map -> IM.singleton modNm <$> map) [modIName..] [map (mfw2qmfw modIName) <$> mixfixHNames]

  -- Note. temporary labelBit allows searching BindNames and labels in 1 Map
  resolver :: M.Map HName (IM.IntMap IName) -- HName -> Modules with that hname
  resolver = let
    labelMap = p ^. P.parseDetails . P.labels
    labels = IM.singleton modIName . (`setBit` labelBit) <$> labelMap
    localNames = p ^. P.parseDetails . P.hNameBinds -- all let-bound HNames
    in M.unionsWith IM.union
      [((\iNms -> IM.singleton modIName iNms) <$> localNames) , curAllNames , labels]

  resolveName :: HName -> ExternVar
  resolveName hNm = let
    binds   = IM.toList <$> (resolver   M.!? hNm)
    mfWords = IM.toList <$> (mfResolver M.!? hNm)
    flattenMFMap = concatMap snd
    in case (binds , mfWords) of
    (Just [] , _)  -> NotInScope hNm -- this name was deleted from (all) modules
    -- inline builtins
    (Just [(modNm , iNm)] , Nothing) -> if
     | modNm == 0 -> Imported $ snd (primBinds V.! iNm)
     | testBit iNm labelBit -> let
--   label applications look like normal bindings `n = Nil`
      q = mkQName modNm (clearBit iNm labelBit)
      sumTy = THSumTy (BSM.singleton (qName2Key q) (TyGround [THTyCon $ THTuple mempty]))
      in Imported $ Core (Label q []) (TyGround [THTyCon sumTy])
     | True -> readQName curMods modNm iNm
    (b , Just mfWords) -> MixfixyVar $ case b of
      Nothing      -> Mixfixy Nothing              (flattenMFMap mfWords)
      Just [(m,i)] -> Mixfixy (Just (mkQName m i)) (flattenMFMap mfWords)
    (Nothing      , Nothing) -> NotInScope hNm
    (Just many , _)          -> AmbiguousBinding hNm many

  in (resolver , mfResolver , Externs (resolveName <$> iMap2Vector (p ^. P.parseDetails . P.hNamesNoScope)))

--tryLockFile "/path/to/directory/.lock" >>= maybe (ko) (ok *> unlockFile)
isCachedFileFresh fName cache =
  (<) <$> getModificationTime fName <*> getModificationTime cache

judge :: Deps -> PureRegistry -> Externs -> ModIName -> P.Module
  -> Either (Errors , JudgedModule) JudgedModule
judge deps reg exts modIName p = let
  bindNames = p ^. P.bindings & \case
    P.LetIn (P.Block _ _ binds) Nothing -> P._fnNm <$> binds
    x -> error (show x)
  labelHNames = p ^. P.parseDetails . P.labels
  (modTT , errors) = judgeModule p deps modIName exts reg._loadedModules
  jm = JudgedModule modIName (p ^. P.moduleName) bindNames (iMap2Vector labelHNames) modTT
  coreOK = null (errors ^. biFails) && null (errors ^. scopeFails) && null (errors ^. checkFails)
    && null (errors ^. typeAppFails) && null (errors ^. mixfixFails)
  in if coreOK then Right jm else Left (errors , jm)

putErrors :: Handle -> Maybe SrcInfo -> BindSource -> Errors -> IO ()
putErrors h srcInfo bindSrc errors = let
  e = [ formatMixfixError srcInfo        <$> (errors ^. mixfixFails)
      , formatBisubError bindSrc srcInfo <$> (errors ^. biFails)
      , formatScopeError                 <$> (errors ^. scopeFails)
      , formatCheckError bindSrc         <$> (errors ^. checkFails)
      , formatTypeAppError               <$> (errors ^. typeAppFails)]
  in T.IO.hPutStr h (T.unlines $ T.unlines <$> filter (not . null) e)
