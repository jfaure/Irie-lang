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
import Text.Megaparsec (errorBundlePretty , ParseErrorBundle)
import ModulePaths
import Errors
import MixfixSyn
import Mixfix
import Externs hiding (Import)
import qualified BitSetMap as BSM
import Data.List (words, isPrefixOf)
import Data.Tree
import Data.Time
import Data.Functor.Base
import Data.Functor.Foldable
import Data.Monoid
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
import Control.Concurrent.MVar
import Control.Monad.Trans
import System.Console.Haskeline ( defaultSettings, getInputLine, runInputT )
import System.Directory ( createDirectoryIfMissing, doesFileExist, getModificationTime )
import System.FileLock
import qualified System.IO as SIO (hClose)

searchPath = ["./" , "ii/"]
objPath    = ["./"]
objDir     = ".irie-obj/"
g_noCache  = True
doFuse     = True
cacheVersion = 0
registryFName = ""

-- ## Deps: build dep-tree > parallel judge dep-tree
--   ? Write ↓↑deps to registry
--   ? return a (Tree ModIName)
-- ## IConv: Must use registry ModINames (else β for trans imports too complicated)
--   => Modules depend on Registry modINames and Registry becomes inflexible
--     * Merge 2 registries requires renaming QNames in all modules in one of them
--     * All deps must be RegINamed before processing (Cannot seal dep-tree)
--     * INames (iconv) vs BindNames (module bindVector elements)
-- ## RegMap : Global bind-lookup (HName -> IMap INames)
--   * If mod IConv changes; need to also update regMap (use oldHNames to find them)
-- ## resolveImports:
--   ?! ImportedSig: BitSet of imported binds from each module (depends on scope)
--   * Optimiser must wait until all modules judged - to avoid copying the Resolver

-- TODO: Registry is MVar; LMV is IOVector ; Register ModIName & init ImportName slot in lmv
-- LMV: readable by resolveName (? MVector read) when not fully initialised
-- Registry Uses
--   >  init , register modules (Parsed / Judged / optimised)
--   <  resolveNames
--   <  search Name / type
--   <> Cache
-- TODO ! need to thread resolver from deps down
--   => Build dep tree and collect leaves
--   => compile leaves and follow dependents (? but only requested ones)
-- TODO print dep-tree
-- TODO Append module (for repl) & suspended parse & parse Expr
-- TODO labelHNames : Bitset of INames indicating which bindNames are labels
-- TODO safe against multiple iries using same cache (lockFile)
-- TODO Import loops: Need to concat parsed modules => _mutMod { open m2Def ; open m2Def }
--   How to merge IConvs ?!
-- TODO Trans imports: Does β-env need entire Registry?

type Deps = BitSet
type Dependents = BitSet
type RegIName = IName -- module IName convention used by current registry (modules have their own local conventions)

-- Note. We read builtins directly , this just occupies Module Name 0
primJM = V.unzip primBinds & \(primHNames , _prims) ->
  let letBinds = LetBlock mempty -- (\x -> _ :: _) <$> prims
  in JudgedModule 0 "Builtins" primHNames primLabelHNames (Core Question tyBot)

-- TODO ? should all have a RegIName
data Import
 = ImportName Text
 | NoPath  Text
 | NoParse Text (ParseErrorBundle Text Void)
 | ImportLoop BitSet -- All deps known; but the loop must be handled specially
 | ParseOK RegIName P.Module -- P.Module contains the filepath
 | JudgeOK RegIName JudgedModule
 | NoJudge RegIName Errors
-- | Cached  RegIName FilePath
 | IRoot -- For compiling multiple files on cmdline without a root module

data LoadedMod = LoadedMod
  { _deps :: Deps
  , _dependents :: Dependents
  , _loadedImport :: Import }; makeLenses ''LoadedMod
data Registry = Registry {
-- 1. A convention for INaming modules at the top-level
-- 2. Track dependency tree (! Modules know their import-list : [HName] , but not their dependents)
-- 3. Efficient bind/type lookup through all loaded modules
-- 4. Tracks file freshness and read/writes to cache
   _modNames          :: M.Map HName IName
 , _allNames          :: M.Map HName (IM.IntMap IName) -- HName -> ModIName -> IName
 , _globalMixfixWords :: M.Map HName (IM.IntMap [QMFWord])
 , _loadedModules     :: V.Vector LoadedMod
  -- ! refreshing cache / rewriting old modules may mess up dependents
}; makeLenses ''Registry
--deriving instance Generic LoadedMod
--deriving instance Generic Registry
--instance DB.Binary LoadedMod
--instance DB.Binary Registry

builtinRegistry = let
  timeBuiltins = UTCTime (ModifiedJulianDay 0) (getTime_resolution)
  lBuiltins = LoadedMod 0 0 (JudgeOK 0 primJM)
  in Registry (M.singleton "Builtins" 0) (IM.singleton 0 <$> primMap) mempty (V.singleton lBuiltins)

initRegistry True  = pure builtinRegistry
initRegistry False = doesFileExist registryFName >>= \case
  True  -> _ -- DB.decodeFile registryFName
  False -> pure builtinRegistry

compileFiles :: CmdLine -> Registry -> [FilePath] -> IO Registry
-- compileFiles cmdLine reg fs = let rootTree = TreeF Root ((0,)<$>fs)
--in mapM (anaM modImports) rootTree `runStateT` (0 , reg)
compileFiles cmdLine reg [f] = buildModTree f `runStateT` (0 , reg)
  >>= \(mT , (_ , reg')) -> reg' <$ judgeTree cmdLine reg' mT

-- Compilation Hylo on Deptree:
-- 1. anaM => check module loops, assign registry MINames , passdown dependents
-- 2. cata => register all modules + deps/dependents + parallel judge modules

type PathFound a = Either a a
type ImportTreeM = StateT (BitSet , Registry) IO

buildModTree :: FilePath -> ImportTreeM (Tree (Dependents , Import))
buildModTree fName = liftIO (findModule searchPath (toS fName))
  >>= \fPath -> anaM modImports (0 , fPath)

-- Note. Prefer to stage a deptree rather than register it instantly
-- , so deps/ents are known and to avoid incremental appends to the Registry
type MISeed = (Dependents , PathFound FilePath)
modImports :: MISeed -> ImportTreeM (TreeF (Dependents , Import) MISeed)
modImports (ds , iPath) = (pathKO ||| pathOK) iPath where
  pathKO fPath = pure (NodeF (ds , NoPath (T.pack fPath)) [])
  pathOK :: FilePath -> ImportTreeM (TreeF (Dependents , Import) (MISeed))
   -- assign a regIName to new modules & check loops
  pathOK fPath = use (_2 . modNames) >>= \mp -> let iM = M.size mp
    in case M.insertLookupWithKey (\_k _new old -> old) (T.pack fPath) iM mp of
      (Just iM , _mp) -> use _1 >>= \iStack -> case iStack `testBit` iM of
        True  -> pure $ NodeF (ds , ImportLoop iStack) []
        False -> use (_2 . loadedModules) >>= \lms -> (lms V.! iM) & \loaded ->
          case True of -- is cached file fresh?
            True  -> pure $ NodeF (ds , loaded._loadedImport) [] -- []: deps already registered
            False -> importOK iM fPath
      (Nothing , mp) -> (_2 . modNames .= mp) *> (_1 %= (`setBit` iM)) *> importOK iM fPath
  importOK :: IName -> FilePath -> ImportTreeM (TreeF (Dependents , Import) MISeed)
  importOK iM fPath = liftIO (T.IO.readFile fPath) <&> parseModule fPath >>= \case
    Left parseKO -> pure (NodeF (ds , NoParse (T.pack fPath) parseKO) [])
    Right p -> (liftIO ((findModule searchPath . toS) `mapM` (p ^. P.imports)))
      <&> \imports -> NodeF (ds , ParseOK iM p) ((ds , ) <$> imports)

-- cata DepTree => register all modules + deps/dependents + parallel judge modules
-- TODO ! need to thread resolver from deps down
judgeTree :: CmdLine -> Registry -> Tree (Dependents , Import) -> IO Registry
judgeTree cmdLine reg modTree = let
  doParallel = False
  nMods = M.size reg._modNames
  -- return the indices (regINames) of updated modules
  -- TODO return dependencies & (At build: passdown dependents)
  judgeTreeF :: V.Vector (MVar LoadedMod)
             -> TreeF (Dependents , Import) (IO (Deps , BitSet))
             -> IO (Deps , BitSet)
  judgeTreeF modMVars (NodeF (deps , mod) xs) = (if doParallel then _ else sequence xs) >>= \rets -> 
    let xsI@(xD , xU) = foldr (\(a,b) (x,y) -> (a.|.x , b.|.y)) (deps , 0) rets :: (Deps , BitSet) in case mod of
    NoPath fName -> xsI <$ putStrLn ("Not found: \"" <> fName <> "\"")
    NoParse fName parseError -> xsI <$ putStrLn (errorBundlePretty parseError)
    JudgeOK mI jm -> pure (xD , setBit xU mI)
    ParseOK mI pm -> let mV = modMVars V.! mI in isEmptyMVar mV >>= \case -- TODO or fresh
      True  -> let
        j = judge cmdLine deps reg (resolveNames reg mI pm) pm mI
        putMod = putMVar mV . LoadedMod deps xD
        in (xD , setBit xU mI) <$ case j of
          Left (errs , _jm) -> putMod (NoJudge mI errs)
            *> putErrors stdout Nothing errs
            *> putStrLn @Text ("KO \"" <> pm ^. P.moduleName <> "\"(" <> show mI <> ")")
          Right jm -> putMod (JudgeOK mI jm)
            *> putJudgedModule cmdLine jm
            *> putStrLn @Text ("OK \"" <> pm ^. P.moduleName <> "\"(" <> show mI <> ")")
      False -> pure xsI
    ImportLoop ms -> error $ "import loop: " <> show (bitSet2IntList ms)
    NoJudge mI jm -> pure xsI
    IRoot -> error "root"
  in do
  modMVars <- V.replicateM nMods newEmptyMVar
  newMods  <- cata (judgeTreeF modMVars) modTree
  regVM    <- V.thaw reg._loadedModules
    >>= \regV' -> MV.grow regV' (nMods - MV.length regV')
  bitSet2IntList (fst newMods) `forM_` \i ->
    readMVar (modMVars V.! i) >>= MV.write regVM i
  regV <- V.freeze regVM
  pure (reg & loadedModules .~ regV)

putJudgedModule cmdLine jm = let
  bindSrc = Nothing
  outHandle = stdout
  putBind = not $ "types" `elem` printPass cmdLine 
  renderOpts = ansiRender { bindSource = bindSrc , ansiColor = not (noColor cmdLine) }
  putJM = True -- ("core" `elem` printPass flags || "opt" `elem` printPass flags)
  in when putJM $ TL.IO.hPutStrLn outHandle (prettyJudgedModule putBind renderOpts jm)

-- * Add bindNames and local labelNames to resolver
-- * Generate Externs vector
resolveNames :: Registry -> IName -> P.Module -> Externs
resolveNames reg modIName p = let
  mixfixHNames = p ^. P.parseDetails . P.hNameMFWords . _2
  curMFWords = reg._globalMixfixWords
  mfResolver = M.unionWith IM.union curMFWords $ M.unionsWith IM.union $
    zipWith (\modNm map -> IM.singleton modNm <$> map) [modIName..] [map (mfw2qmfw modIName) <$> mixfixHNames]

  -- Note. temporary labelBit allows searching BindNames and labels in 1 Map
  resolver :: M.Map HName (IM.IntMap IName) -- HName -> Modules with that hname
  resolver = let
    labelMap = p ^. P.parseDetails . P.labels
    labels = IM.singleton modIName . (`setBit` labelBit) <$> labelMap
    localNames = p ^. P.parseDetails . P.hNameBinds -- all let-bound HNames
    in M.unionsWith IM.union
      [((\iNms -> IM.singleton modIName iNms) <$> localNames) , reg._allNames , labels]

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
     | True -> Importable modNm iNm
    (b , Just mfWords) -> MixfixyVar $ case b of
      Nothing      -> Mixfixy Nothing              (flattenMFMap mfWords)
      Just [(m,i)] -> Mixfixy (Just (mkQName m i)) (flattenMFMap mfWords)
    (Nothing      , Nothing) -> NotInScope hNm
    (Just many , _)          -> AmbiguousBinding hNm many

  -- convert noScopeNames map to a vector (Map HName IName -> Vector HName)
  names :: Map HName Int -> V.Vector ExternVar
  names noScopeNames = V.create $ MV.unsafeNew (M.size noScopeNames)
    >>= \v -> v <$ (\nm idx -> MV.write v idx $ resolveName nm) `M.traverseWithKey` noScopeNames

  in Externs
    { extNames = resolveName <$> iMap2Vector (p ^. P.parseDetails . P.hNamesNoScope)
    -- v The point is local labels may be imported
    -- ? TODO do we always create a new label if @ used
    -- parsedLabels = parsed ^. P.parseDetails . P.labels
--  , importLabels = mempty -- : Vector QName ; Rename INames to imported QNames
    }

registerJudgedModule :: Registry -> JudgedModule -> Registry
registerJudgedModule reg j = _

--tryLockFile "/path/to/directory/.lock" >>= maybe (ko) (ok *> unlockFile)
isCachedFileFresh fName cache =
  (<) <$> getModificationTime fName <*> getModificationTime cache

printDepTree mI = _ -- read deps from flat registry

judge :: CmdLine -> Deps -> Registry -> Externs -> P.Module -> RegIName
  -> Either (Errors , JudgedModule) JudgedModule
judge cmdLine deps reg exts p modIName = let
  bindNames     = p ^. P.bindings & \case
    P.LetIn (P.Block _ _ binds) Nothing -> P._fnNm <$> binds
    x -> error (show x)
  labelHNames = p ^. P.parseDetails . P.labels
  (modTT , errors) = judgeModule p deps modIName exts
  jm = JudgedModule modIName (p ^. P.moduleName) bindNames (iMap2Vector labelHNames) modTT
  coreOK = null (errors ^. biFails) && null (errors ^. scopeFails) && null (errors ^. checkFails)
    && null (errors ^. typeAppFails) && null (errors ^. mixfixFails)
  in if coreOK then Right jm else Left (errors , jm)

putErrors :: Handle -> Maybe SrcInfo -> Errors -> IO ()
putErrors h srcInfo errors = let
  bindNames = mempty -- V.zip bindNames judgedBinds
  bindSrc = BindSource mempty bindNames _iNamesV (_labelHNames _r) (__allBinds _r)
  e = [ formatMixfixError srcInfo        <$> (errors ^. mixfixFails)
      , formatBisubError bindSrc srcInfo <$> (errors ^. biFails)
      , formatScopeError                 <$> (errors ^. scopeFails)
      , formatCheckError bindSrc         <$> (errors ^. checkFails)
      , formatTypeAppError               <$> (errors ^. typeAppFails)]
  in T.IO.hPutStr h (T.unlines $ T.unlines <$> filter (not . null) e)


