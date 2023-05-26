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
import Data.Functor.Base
import qualified Data.Text as T
import qualified Data.Text.IO as T.IO
import qualified Data.Text.Lazy.IO as TL.IO
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Map.Strict as M
import qualified Data.IntMap as IM
import Control.Lens
import Control.Concurrent.Async
import System.Directory ( doesFileExist , getModificationTime )
import qualified Fresnel.Lens as F
import qualified Fresnel.Setter as F
import qualified System.IO as SIO -- (hClose , openTempFile)
--import System.FileLock
--import qualified Data.Binary as DB

searchPath = ["./" , "ii/"]
objPath    = ["./"]
objDir     = ".irie-obj/"
g_noCache  = True
doFuse     = True
cacheVersion = 0
registryFName = ""
doParallel = False

-- Text.EditDistance> levenshteinDistance defaultEditCosts "witch" "kitsch"

-- ## Deps: build dep-tree > parallel judge dep-tree & Write ↓↑deps to registry
-- ## IConv: Must use registry ModINames (else β for trans imports too complicated)
--   => Modules depend on Registry modINames and Registry becomes inflexible
--     * Merge 2 registries requires renaming QNames in all modules in one of them
--     * All deps must be ModINamed before processing (Cannot seal dep-tree)
--     * INames (iconv) vs BindNames (module bindVector elements)
-- ## RegMap : Global bind-lookup (HName -> IMap INames)
--   * If mod IConv changes; need to also update regMap (use oldHNames to find them)

-- TODO When exactly print stuff
-- TODO search(fuzzy?) Registry (hackage edit-distance)
-- TODO print dep-tree (also needsRecompile tree)
-- TODO Append module (for repl) & suspended parse & parse Expr
-- TODO cache (lockfile) , CachedModule = Import
-- TODO Import loops: Need to concat parsed modules => _mutMod { open m2Def ; open m2Def }
--   How to merge IConvs ?!
-- TODO mergeRegistries
-- TODO ImportedSig: BitSet of imported binds from each module (depends on scope)

lookupIName     = lookupJM labelNames
lookupFieldName = lookupJM jmINames
lookupJM jmProj lms mName iName = case _loadedImport (lms V.! mName) of
  JudgeOK _mI jm -> Just (jmProj jm V.! iName)
  _ -> Nothing

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
    (Nothing , mp)  -> Right iM <$ do
      queued <- newEmptyMVar
      putMVar reg' (reg & modNames .~ mp & loadedModules %~ (`V.snoc` (LoadedMod 0 0 (ImportQueued queued))))

data InCompile = InText Text | InFilePath (Either FilePath FilePath) deriving Show

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
--        False -> parseFileImports iM fPath
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

registerDeps :: Registry -> ModuleIName -> Deps -> Dependents -> IO ()
registerDeps reg mI deps dents = takeMVar reg >>= \r -> let
  addDeps (LoadedMod deps' dents' m) = LoadedMod (deps .|. deps') (dents .|. dents') m
  in putMVar reg (r & loadedModules %~ V.modify (\v -> MV.modify v addDeps mI))

-- Add bindNames to allBinds!
--registerJudgedMod :: Registry -> ModIName -> Either Errors (_ , _ , JudgedModule) -> IO ()
registerJudgedMod reg mI modOrErrors = let
  addMod jm (LoadedMod deps dents _m) = LoadedMod deps dents (JudgeOK mI jm)
  addJM (resolver , mfResolver , jm) = takeMVar reg >>= \r -> putMVar reg (
    r & loadedModules %~ V.modify (\v -> MV.modify v (addMod jm) mI)
      & Externs.allNames .~ resolver
      & Externs.globalMixfixWords .~ mfResolver
    )
  in do
    getLoadedModule reg mI <&> _loadedImport >>= \case
      ImportQueued mvar -> putMVar mvar ()
      _ -> pure ()
    (const (pure ()) ||| addJM) modOrErrors

simplify :: CmdLine -> JudgedModule -> JudgedModule
simplify cmdLine jm = if noFuse cmdLine then jm else let
  mL :: F.Lens' JudgedModule Expr
  mL = F.lens moduleTT (\u new -> u { moduleTT = new })
  in jm & mL F.%~ (\e -> runST (BetaEnv.simpleExpr e))

-- cata DepTree => parallel judge modules , register all modules and deps/dependents
judgeTree :: CmdLine -> Registry -> TreeF (Dependents , Import) (IO Deps) -> IO Deps
judgeTree cmdLine reg (NodeF (dependents , mod) m_depL) = mapConcurrently identity m_depL
  >>= \depL -> let deps = foldr (.|.) 0 depL in case mod of
  NoPath fName -> deps <$ putStrLn ("Not found: \"" <> fName <> "\"")
  NoParse _fName parseError -> deps <$ putStrLn (errorBundlePretty parseError)
  JudgeOK mI _j -> setBit dependents mI <$ registerDeps reg mI deps dependents
  ParseOK mI pm -> when ("parseTree" `elem` printPass cmdLine) (putStrLn (P.prettyModule pm))
    *> readMVar reg >>= \reg' -> deps <$ -- setBit dependents mI
    let iNamesV = iMap2Vector (pm ^. P.parseDetails . P.hNamesToINames)
        (resolver , mfResolver , exts) = resolveNames reg' mI pm iNamesV
        getBindSrc = readMVar reg <&> \r -> -- Need to read this after registering current module
          BindSource (lookupIName r._loadedModules) (lookupFieldName r._loadedModules)
        putModVerdict = False -- TODO should only print at repl?
        (warnings , jmResult) = judge deps reg' exts mI pm iNamesV
    in case simplify cmdLine <$> jmResult of
      -- TODO have partially OK judged module
      Left (errs , _jm) -> registerJudgedMod reg mI (Left errs)
        *> getBindSrc >>= \bindSrc ->
        putErrors stdout Nothing bindSrc errs
        *> when putModVerdict (putStrLn @Text ("KO \"" <> pm ^. P.moduleName <> "\"(" <> show mI <> ")"))
      Right jm -> let
        shouldPutJM = (dependents == 0 || putDependents cmdLine)
                       && any (`elem` printPass cmdLine) ["core", "simple", "types"]
        in registerJudgedMod reg mI (Right (resolver , mfResolver , jm))
        *> maybe (pure ()) putStrLn warnings
        *> when shouldPutJM (getBindSrc >>= \bindSrc -> putJudgedModule cmdLine (Just bindSrc) jm)
        *> when putModVerdict (putStrLn @Text ("OK \"" <> pm ^. P.moduleName <> "\"(" <> show mI <> ")"))
  ImportLoop ms -> error $ "import loop: " <> show (bitSet2IntList ms)
  NoJudge _mI _jm -> pure deps
  IRoot -> error "root"
  ImportQueued m -> readMVar m $> deps
  -- Wait. TODO IMPORTANT! This will hang if ImportQueued thread fails to putMVar (call registerJudgedMod)

putJudgedModule :: CmdLine -> Maybe BindSource -> JudgedModule -> IO ()
putJudgedModule cmdLine bindSrc jm = let
  putBind = not $ "types" `elem` printPass cmdLine 
  renderOpts = ansiRender { bindSource = bindSrc , ansiColor = not (noColor cmdLine) }
  putJM outHandle = TL.IO.hPutStrLn outHandle (prettyJudgedModule putBind renderOpts jm)
  in case cmdLine.outFile of
    Nothing    -> putJM stdout
    Just fName -> openFile fName WriteMode >>= \h -> putJM h *> SIO.hClose h

-- * Add bindNames and local labelNames to resolver
-- * Generate Externs vector
resolveNames :: PureRegistry -> IName -> P.Module -> V.Vector HName
  -> (M.Map HName (IntMap IName) , M.Map HName (IM.IntMap [QMFWord]) , Externs)
resolveNames reg modIName p iNamesV = let
  curAllNames = reg._allNames
  curMFWords  = reg._globalMixfixWords
  curMods     = reg._loadedModules
  mixfixHNames = p ^. P.parseDetails . P.hNameMFWords
  mfResolver = M.unionWith IM.union curMFWords $ M.unionsWith IM.union $
    zipWith (\modNm map -> IM.singleton modNm <$> map) [modIName..] [map (mfw2qmfw modIName) <$> mixfixHNames]

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
     | True -> maybe (Importable modNm iNm) Imported (readQName curMods modNm iNm)
    (b , Just mfWords) -> let flattenMFMap = concatMap snd in MixfixyVar $ case b of
      Nothing      -> Mixfixy Nothing              (flattenMFMap mfWords)
      Just [(m,i)] -> Mixfixy (Just (mkQName m i)) (flattenMFMap mfWords)
      _ -> error "TODO"
    (Nothing      , Nothing) -> NotInScope hNm
    (Just many , _)          -> AmbiguousBinding hNm many

  in (resolver , mfResolver , Externs (resolveName <$> iNamesV))

--tryLockFile "/path/to/directory/.lock" >>= maybe (ko) (ok *> unlockFile)
isCachedFileFresh fName cache =
  (<) <$> getModificationTime fName <*> getModificationTime cache

judge :: Deps -> PureRegistry -> Externs -> ModIName -> P.Module -> V.Vector HName
  -> (Maybe Text , Either (Errors , JudgedModule) JudgedModule)
judge deps reg exts modIName p iNamesV = let
--  bindNames   = p ^. P.bindings <&> P._fnNm
  labelHNames = p ^. P.parseDetails . P.labels
  bindINames  = p ^. P.parseDetails . P.topINames
  (modTT , errors) = judgeModule p deps modIName exts reg._loadedModules
  jm = JudgedModule modIName (p ^. P.moduleName) (iMap2Vector labelHNames) iNamesV bindINames modTT
  coreOK = null (errors ^. biFails) && null (errors ^. scopeFails) && null (errors ^. checkFails)
    && null (errors ^. typeAppFails) && null (errors ^. mixfixFails) && null (errors ^. unpatternFails)
  warnings = errors ^. scopeWarnings & \ws -> if null ws then Nothing
    else Just (unlines $ formatScopeWarnings iNamesV <$> ws)
  in (warnings , if coreOK then Right jm else Left (errors , jm))

putErrors :: Handle -> Maybe SrcInfo -> BindSource -> Errors -> IO ()
putErrors h srcInfo bindSrc errors = let
  e = [ formatMixfixError srcInfo        <$> (errors ^. mixfixFails)
      , formatBisubError bindSrc srcInfo <$> (errors ^. biFails)
      , formatScopeError                 <$> (errors ^. scopeFails)
      , formatCheckError bindSrc         <$> (errors ^. checkFails)
      , formatTypeAppError               <$> (errors ^. typeAppFails)
      , formatUnPatError                 <$> (errors ^. unpatternFails)]
  in T.IO.hPutStr h (T.unlines $ T.unlines <$> filter (not . null) e)
