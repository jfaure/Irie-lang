{-# Language TemplateHaskell #-}
module Registry where
import CmdLine
import CoreSyn
import MixfixSyn(QMFWord)
import qualified ParseSyntax as P
import Parser (parseModule)
import CoreBinary()
import PrettyCore
import Infer(judgeModule)
import qualified BetaEnv(simpleBindings)
import qualified Elf
import qualified CoreToX86
import Text.Megaparsec (errorBundlePretty)
import ModulePaths
import Errors
import Externs
import Data.Functor.Base
import qualified Data.Text as T
import qualified Data.Text.IO as T.IO
import qualified Data.Text.Lazy.IO as TL.IO
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Mutable as MV
import qualified Data.Map.Strict as M
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

-- TODO search(fuzzy?) Registry (hackage edit-distance)
-- TODO print dep-tree (also needsRecompile tree)
-- TODO Append module (for repl) & suspended parse & parse Expr
-- TODO cache (lockfile) , CachedModule = Import
-- TODO Import loops: Need to concat parsed modules => _mutMod { open m2Def ; open m2Def }
--   How to merge IConvs ?!
-- TODO mergeRegistries
-- TODO ImportedSig: BitSet of imported binds from each module (depends on scope)

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

-- must call findModule on import statements to normalise the key
resolveModuleHName :: PureRegistry -> HName -> IName
resolveModuleHName reg textModName = fromMaybe (error ("module unknown! " <> show textModName)) (_modNames reg M.!? textModName)

compileText :: CmdLine -> Registry -> Text -> IO (Maybe Import)
compileText cmdLine reg progText = do
  void $ join (hyloM (judgeTree cmdLine reg) (readDeps reg) (0 , InText progText))
  modIName <- readMVar reg <&> \r -> resolveModuleHName r textModName
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
    Right p -> ((fmap InFilePath . findModule searchPath . toS) `mapM` (catMaybes $ P.getImportFile <$> (p ^. P.imports))) <&> \imports ->
--    <&> \imports -> let hackImports = concatMap (\case {InText{}->[] ; InFilePath e -> (const [] ||| (\x->[toS x])) e}) imports
      NodeF (ds , ParseOK txt iM p) ((setBit ds iM , ) <$> imports)
  in case input of
  InText txt -> registerModule reg textModName
    >>= \iM -> inText ((identity ||| identity) iM) (T.unpack textModName) txt
  InFilePath iPath -> (pathKO ||| pathOK) iPath

registerDeps :: Registry -> ModuleIName -> Deps -> Dependents -> IO ()
registerDeps reg mI deps dents = takeMVar reg >>= \r -> let
  addDeps (LoadedMod deps' dents' m) = LoadedMod (deps .|. deps') (dents .|. dents') m
  in putMVar reg (r & loadedModules %~ V.modify (\v -> MV.modify v addDeps mI))

-- Add bindNames to allBinds!
registerJudgedMod :: Registry -> ModIName
  -> Either Errors (Map HName (IntMap IName) , Map HName (IntMap [QMFWord]) , JudgedModule) -> IO ()
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

-- cata DepTree => parallel judge modules , register all modules and deps/dependents
judgeTree :: CmdLine -> Registry -> TreeF (Dependents , Import) (IO Deps) -> IO Deps
judgeTree cmdLine reg (NodeF (dependents , mod) m_depL) = mapConcurrently identity m_depL
  >>= \depL -> let deps = foldr (.|.) 0 depL in case mod of
  NoPath fName -> deps <$ putStrLn ("Not found: \"" <> fName <> "\"")
  NoParse _fName parseError -> deps <$ putStrLn (errorBundlePretty parseError)
  JudgeOK mI _j -> setBit deps mI <$ registerDeps reg mI deps dependents
  ParseOK progText mI pm -> do
   when ("parseTree" `elem` printPass cmdLine) (putStrLn (P.prettyModule pm))
   regPreImports <- readMVar reg
   importINames <- let
     go acc f = case P.getImportFile f of
       Nothing -> pure acc
       Just h -> findModule searchPath (toS h) <&> (const acc ||| setBit acc . resolveModuleHName regPreImports . toS)
     in foldM go 0 (pm ^. P.imports)
   reg' <-  readMVar reg
   setBit deps mI <$ let -- setBit dependents mI
     iNamesV = V.fromList (reverse (pm ^. P.parseDetails . P.hNamesToINames . _2))
     -- iMap2Vector (pm ^. P.parseDetails . P.hNamesToINames)
     (resolver , mfResolver , exts) = resolveNames reg' mI pm iNamesV
     getBindSrc = readMVar reg <&> \r -> -- Need to read this after registering current module
       BindSource (lookupIName r._loadedModules) (lookupBindName r._loadedModules)
     srcInfo = Just (SrcInfo progText (VU.reverse $ VU.fromList $ pm ^. P.parseDetails . P.newLines))
     putModVerdict = False -- TODO should only print at repl?
     (warnings , jmResult) = judge importINames reg' exts mI pm iNamesV

     shouldSimplify = not $ (noFuse cmdLine || elem "core" (printPass cmdLine) || elem "types" (printPass cmdLine))
     in case if shouldSimplify then simplify cmdLine mI reg'._loadedModules <$> jmResult else jmResult of
     -- Note. we still register the module even though its is partially broken, esp. for putErrors to lookup names
     Left (errs , jm) -> registerJudgedMod reg mI (Right (resolver , mfResolver , jm))
       *> getBindSrc >>= \bindSrc ->
       putErrors stdout mI srcInfo bindSrc errs
       *> {-when putModVerdict-} (putStrLn @Text ("KO \"" <> pm ^. P.moduleName <> "\"(" <> show mI <> ")"))
     Right jm -> let
       shouldPutJM = (dependents == 0 || putDependents cmdLine)
                      && any (`elem` printPass cmdLine) ["core", "simple", "types"]
       -- TODO when to do elf stuff
       shouldMkElf = putX86 cmdLine -- shouldSimplify
       disassElf = True
       runElf = True
       coreToAsm curReg maybeMain = CoreToX86.mkAsmBindings mI curReg._loadedModules maybeMain jm.moduleTT
       lookupMain r' = findBindIndex r' mI "main"
       in registerJudgedMod reg mI (Right (resolver , mfResolver , jm))
       *> maybe (pure ()) putStrLn warnings
       *> when shouldPutJM (getBindSrc >>= \bindSrc -> putJudgedModule cmdLine (Just bindSrc) jm)
       *> when shouldMkElf (readMVar reg >>= \r' -> Elf.mkElf (disassElf , runElf) (coreToAsm r' (lookupMain r')))
       *> when putModVerdict (putStrLn @Text ("OK \"" <> pm ^. P.moduleName <> "\"(" <> show mI <> ")"))
  ImportLoop ms -> error $ "import loop: " <> show (bitSet2IntList ms)
  NoJudge _mI _jm -> pure deps
  IRoot -> error "root"
  ImportQueued m -> deps <$ readMVar m -- Wait.
  -- IMPORTANT! This will hang if ImportQueued thread fails to putMVar (call registerJudgedMod)

--tryLockFile "/path/to/directory/.lock" >>= maybe (ko) (ok *> unlockFile)
isCachedFileFresh fName cache =
  (<) <$> getModificationTime fName <*> getModificationTime cache

judge :: Deps -> PureRegistry -> Externs -> ModIName -> P.Module -> V.Vector HName
  -> (Maybe Text , Either (Errors , JudgedModule) JudgedModule)
judge deps reg exts modIName p iNamesV = let
--  bindNames   = p ^. P.bindings <&> P._fnNm
  labelINames = p ^. P.parseDetails . P.labelINames
  bindINames  = p ^. P.parseDetails . P.topINames
  modOpens    = p ^. P.imports
  (modTT , errors) = judgeModule p deps modIName exts reg._loadedModules
  openDatas = mempty
  jm = JudgedModule modIName (p ^. P.moduleName) iNamesV bindINames labelINames openDatas modTT
  coreOK = null (errors ^. biFails) && null (errors ^. scopeFails) && null (errors ^. checkFails)
    && null (errors ^. typeAppFails) && null (errors ^. mixfixFails) && null (errors ^. unpatternFails)
  warnings = errors ^. scopeWarnings & \ws -> if null ws then Nothing
    else Just (unlines $ formatScopeWarnings iNamesV <$> ws)
  in {-d_ modOpens-} (warnings , if coreOK then Right jm else Left (errors , jm))

simplify :: CmdLine -> ModuleIName -> V.Vector LoadedMod -> JudgedModule -> JudgedModule
simplify _cmdLine thisMod loadedMods jm = let
  mL :: F.Lens' JudgedModule ModuleBinds -- Fresnel experiment
  mL = F.lens moduleTT (\u new -> u { moduleTT = new })
  in jm & mL F.%~ (\e -> runST (BetaEnv.simpleBindings thisMod loadedMods e))

putJudgedModule :: CmdLine -> Maybe BindSource -> JudgedModule -> IO ()
putJudgedModule cmdLine bindSrc jm = let
  putBind = not $ "types" `elem` printPass cmdLine
  renderOpts = ansiRender { bindSource = bindSrc , ansiColor = not (noColor cmdLine) }
  putJM outHandle = TL.IO.hPutStrLn outHandle (prettyJudgedModule (putLetBinds cmdLine) putBind renderOpts jm)
  in case cmdLine.outFile of
    Nothing    -> putJM stdout
    Just fName -> openFile fName WriteMode >>= \h -> putJM h *> SIO.hClose h

putErrors :: Handle -> ModuleIName -> Maybe SrcInfo -> BindSource -> Errors -> IO ()
putErrors h thisMod srcInfo bindSrc errors = let
  e = [ formatMixfixError srcInfo        <$> (errors ^. mixfixFails)
      , formatBisubError bindSrc srcInfo <$> (errors ^. biFails)
      , formatScopeError thisMod bindSrc <$> (errors ^. scopeFails)
      , formatCheckError bindSrc         <$> (errors ^. checkFails)
      , formatTypeAppError               <$> (errors ^. typeAppFails)
      , formatUnPatError                 <$> (errors ^. unpatternFails)]
  in T.IO.hPutStr h (T.unlines $ T.unlines <$> filter (not . null) e)
