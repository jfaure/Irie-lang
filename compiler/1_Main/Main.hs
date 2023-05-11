-- main = Text >> Parse >> Core >> STG >> LLVM
module Main where
import CmdLine
import qualified ParseSyntax as P
import Parser (parseModule)
import ModulePaths (findModule)
import Externs (Externs(..) , GlobalResolver(..) , ModDependencies(..) , ModDeps , primResolver , addModuleToResolver , resolveImports , addModName , addDependency)
import CoreSyn
import CoreUtils (bind2Expr)
import Errors
import CoreBinary()
import PrettyCore
import qualified PrettySSA
import Infer (judgeModule)
import qualified BetaEnv (simpleExpr)
import MkSSA (mkSSAModule)
import C (mkC)

import Text.Megaparsec ( errorBundlePretty )
import qualified Data.Text as T
import qualified Data.Text.IO as T.IO
import qualified Data.Text.Lazy.IO as TL.IO
import qualified Data.Text.Lazy as TL
import qualified Data.ByteString.Lazy as BSL.IO
import qualified Data.Vector as V
import qualified Data.Map    as M
import qualified Data.Vector.Unboxed as VU
import qualified Data.Binary as DB
import Control.Lens -- ( (^.), Field2(_2) )
import System.Console.Haskeline ( defaultSettings, getInputLine, runInputT )
import System.Directory ( createDirectoryIfMissing, doesFileExist, getModificationTime )
import qualified System.IO as SIO (hClose)
import Data.List (words)

searchPath = ["./" , "ii/"]
objPath    = ["./"]
objDir'    = ".irie-obj/"
objDir     = objDir' <> "@" -- prefix '@' to files in there
getCachePath fName = let
  -- ./module == module for cache purposes so they must be converted
  normalise fName = case fName of
    '.' : '/' : _ -> fName
    '/' : _ -> fName
    _ -> '.' : '/' : fName
  in objDir <> map (\case { '/' -> '%' ; x -> x} ) (normalise fName)
resolverCacheFName = getCachePath "resolver"
doCacheCore  = False
doFuse       = True
cacheVersion = 0

deriving instance Generic GlobalResolver
deriving instance Generic Externs
deriving instance Generic ModDependencies
instance DB.Binary GlobalResolver
instance DB.Binary Externs
instance DB.Binary ModDependencies

-- <dead code> for use in ghci
demoFile   = "demo.ii"
sh         = main' . Data.List.words
parseTree  = sh $ demoFile <> " -p parse"
ssa        = sh $ demoFile <> " -p ssa"
core       = sh $ demoFile <> " -p core"
types      = sh $ demoFile <> " -p types"
opt        = sh $ demoFile <> " -p simple"
emitC      = sh $ demoFile <> " -p C"
interp     = sh $ demoFile <> " --interpret"
testRepl   = sh ""

--data Pipeline
--  = PCmdline    (Options.Applicative.Types.ParserResult CmdLine)
--  | PFileExists (Either FilePath FilePath)
--  | PParse      (Either (ParseErrorBundle Text Void) P.Module)
--  | PImports    (Either BitSet P.Module)
--  | PJudge      (Either Errors JudgedModule)
--  | PSimple     JudgedModule

main = getArgs >>= main'
main' args = parseCmdLine args >>= \cmdLine -> do
  when ("args" `elem` printPass cmdLine) (print cmdLine)
  when doCacheCore (createDirectoryIfMissing False objDir')
  resolverExists <- doesFileExist resolverCacheFName
  resolver       <- if doCacheCore && not (noCache cmdLine) && resolverExists
    then DB.decodeFile resolverCacheFName :: IO GlobalResolver
    else pure primResolver -- Strings cmdLine :: IO String programs
  files cmdLine `forM` doFileCached cmdLine True resolver 0
  when (repl cmdLine || null (files cmdLine) && null (strings cmdLine)) $ let
    patchFlags = cmdLine{ printPass = "types" : printPass cmdLine , repl = True , noColor = False , noFuse = True }
    in replCore (if null (printPass cmdLine) then patchFlags else cmdLine)

decodeCoreFile :: FilePath -> IO JudgedModule       = DB.decodeFile
encodeCoreFile :: FilePath -> JudgedModule -> IO () = DB.encodeFile
cacheFile fp jb = createDirectoryIfMissing False objDir *> encodeCoreFile (getCachePath fp) jb

doFileCached :: CmdLine -> Bool -> GlobalResolver -> ModDeps -> FilePath -> IO (GlobalResolver , JudgedModule)
doFileCached flags isMain resolver depStack fName = let
  cached            = getCachePath fName
  isCachedFileFresh = (<) <$> getModificationTime fName <*> getModificationTime cached
  go resolver modNm = doesFileExist fName >>=
    \exists -> unless exists (error ("file does not exist: " <> show fName))
    *>  T.IO.readFile fName
    >>= text2Core flags modNm resolver depStack fName
    >>= putResults . simplifyModule
    >>= codegen flags
  go' resolver = go resolver Nothing
  didIt = modNameMap resolver M.!? toS fName
  in case didIt of
  Just _    | not doCacheCore || noCache flags ->
    error $ "compiling a module twice without cache is unsupported: " <> show fName
  Just modI | depStack `testBit` modI -> error $ "Import loop: "
    <> toS (T.intercalate " <- " (show . (modNamesV resolver V.!) <$> bitSet2IntList depStack))
  _         | not doCacheCore -> go' resolver
  _ -> doesFileExist cached >>= \exists -> if not exists then go' resolver else do
    fresh  <- isCachedFileFresh
    judged <- decodeCoreFile cached :: IO JudgedModule -- even stale cached modules need to be read
    if fresh && not (recompile flags) && not isMain then pure (resolver , judged)
      else let names = bindNames judged <> V.fromList (M.keys (labelNames judged))
        in go resolver (Just $ OldCachedModule (modIName judged) names)
      --else go (rmModule modINm (bindNames judged) resolver) (Just modINm)

evalImports :: CmdLine -> ModIName -> GlobalResolver -> BitSet -> [Text] -> IO (Bool, GlobalResolver, ModDependencies)
evalImports flags moduleIName resolver depStack fileNames = do
  (nopath , importPaths) <- partitionEithers <$> (findModule searchPath . toS) `mapM` fileNames
  nopath `forM_` \f -> putStrLn $ ("couldn't find " <> show f <> " in search path\n" <> show searchPath :: Text)

  -- TODO this foldM could be parallel
  (r , importINames) <- let
    inferImport (res,imports) path = (\(a,j)->(a,modIName j: imports)) <$> doFileCached flags False res depStack path
    in foldM inferImport (resolver , []) importPaths
  let modDeps = ModDependencies { deps = foldl setBit emptyBitSet importINames , dependents = emptyBitSet }
      r' = foldl (\r imported -> addDependency imported moduleIName r) r importINames
  pure (null nopath , r' , modDeps)

-- Parse , judge , simplify a module (depending on cmdline flags)
text2Core :: CmdLine -> Maybe OldCachedModule -> GlobalResolver -> BitSet -> String -> Text
  -> IO (CmdLine, FilePath, JudgedModule, V.Vector HName , GlobalResolver, Externs, Errors, Maybe SrcInfo)
text2Core flags maybeOldModule resolver' depStack fName progText = do
  -- Just moduleIName indicates this module was already cached, so don't allocate a new module iname for it
  let modIName = maybe (modCount resolver') oldModuleIName maybeOldModule
      resolver = if isJust maybeOldModule then resolver' else addModName modIName (T.pack fName) resolver'
  when ("source" `elem` printPass flags) (putStr =<< readFile fName)
  parsed <- case parseModule fName progText of
    Left e  -> putStrLn (errorBundlePretty e) $> P.emptyParsedModule (toS fName) -- TODO add to parse fails
    Right r -> pure r
  when ("parseTree" `elem` printPass flags) (putStrLn (P.prettyModule parsed))

  (importsok , modResolver , modDeps) <- evalImports flags modIName resolver (setBit depStack modIName) (parsed ^. P.imports)
  unless importsok (putStrLn ("some imports KO" :: Text))
  pure $ inferResolve flags fName modIName modResolver modDeps parsed progText maybeOldModule

-- Judge the module and update the global resolver
inferResolve :: CmdLine -> [Char] -> Int -> GlobalResolver -> ModDependencies -> P.Module -> Text -> Maybe OldCachedModule
  -> (CmdLine , FilePath , JudgedModule , V.Vector HName , GlobalResolver , Externs , Errors , Maybe SrcInfo)
inferResolve flags fName modIName modResolver modDeps parsed progText maybeOldModule = let
  hNames     = parsed ^. P.bindings & \case
    P.LetIn (P.Block _ _ binds) Nothing -> P._fnNm <$> binds
    x -> error (show x)
  labelMap   = parsed ^. P.parseDetails . P.labels
  iNames     = parsed ^. P.parseDetails . P.hNamesNoScope
  srcInfo    = Just (SrcInfo progText (VU.reverse $ VU.fromList $ parsed ^. P.parseDetails . P.newLines))

  (tmpResolver  , exts) = resolveImports
    modResolver modIName
    (parsed ^. P.parseDetails . P.hNameBinds)        -- module bindings incl. lets
    labelMap                                         -- HName -> label and field names maps
    (parsed ^. P.parseDetails . P.hNameMFWords . _2) -- mixfix names
    iNames
    maybeOldModule

  (modTT , errors) = judgeModule parsed (deps modDeps) modIName exts
  judgedModule = JudgedModule modIName (parsed ^. P.moduleName) hNames (parsed ^. P.parseDetails . P.labels) modTT

-- TODO add all let-binds to resolver?
--JudgedModule _modIName _modNm bindNames _a _b judgedBinds _specs = judgedModule
  bindExprs = moduleTT judgedModule & \case
    Core (LetBlock binds) _ty -> binds <&> \(meta , e) -> (hName meta , bind2Expr e)
    x -> error (show x) -- V.zip bindNames (bind2Expr <$> judgedBinds)
  newResolver = addModuleToResolver tmpResolver modIName bindExprs (iMap2Vector labelMap) labelMap modDeps
  in (flags , fName , judgedModule , (iMap2Vector iNames) , newResolver , exts , errors , srcInfo)

-- TODO half-compiled modules `not coreOK` should also be cached (since their names were pre-added to the resolver)
simplifyModule :: (CmdLine, f, JudgedModule, V.Vector HName , GlobalResolver, e, Errors, e2)
  -> ( CmdLine, Bool, Errors, e2, f, V.Vector HName , GlobalResolver , JudgedModule)
simplifyModule (flags , fName , judgedModule , iNames , newResolver , _exts , errors , srcInfo) = let
  JudgedModule modI modNm bindNames lMap judgedModTT = judgedModule
  coreOK = null (errors ^. biFails) && null (errors ^. scopeFails)
    && null (errors ^. checkFails) && null (errors ^. typeAppFails) && null (errors ^. mixfixFails)
  skipFuse = not doFuse || noFuse flags || not coreOK || elem "types" (printPass flags)
  judgedSimple = if skipFuse then judgedModule else runST $
    BetaEnv.simpleExpr judgedModTT <&> \modTTSimple
      -> JudgedModule modI modNm bindNames lMap modTTSimple
  in (flags , coreOK , errors , srcInfo , fName , iNames , newResolver , judgedSimple)

putResults :: (CmdLine, Bool, Errors, Maybe SrcInfo , FilePath , V.Vector HName , GlobalResolver , JudgedModule)
  -> IO (GlobalResolver, JudgedModule)
putResults (flags , coreOK , errors , srcInfo , fName , iNamesV , r , j) = let
  raw = not doFuse || noFuse flags || not coreOK || elem "types" (printPass flags) -- TODO same as above
--testPass p = coreOK && p `elem` printPass flags && not (quiet flags)
  putErrors h = do
    T.IO.hPutStr  h $ T.concat  $ (<> "\n\n") . formatMixfixError srcInfo        <$> (errors ^. mixfixFails)
    T.IO.hPutStr  h $ T.concat  $ (<> "\n\n") . formatBisubError bindSrc srcInfo <$> (errors ^. biFails)
    T.IO.hPutStr  h $ T.concat  $ (<> "\n\n") . formatScopeError            <$> (errors ^. scopeFails)
    TL.IO.hPutStr h $ TL.concat $ (<> "\n\n") . formatCheckError bindSrc    <$> (errors ^. checkFails)
    TL.IO.hPutStr h $ TL.concat $ (<> "\n\n") . formatTypeAppError          <$> (errors ^. typeAppFails)

  bindNames = mempty -- V.zip bindNames judgedBinds
  bindSrc = BindSource mempty bindNames iNamesV (labelHNames r) (allBinds r)
  in do
  -- write to stdout unless an outfile was specified -- TODO write errors there also ?!
  outHandle <- case flags.outFile of
    Nothing    -> pure stdout
    Just fName -> openFile fName WriteMode
  putErrors outHandle
  when coreOK $ let
    putBind = not $ "types" `elem` printPass flags
    renderOpts = ansiRender { bindSource = Just bindSrc , ansiColor = not (noColor flags) }
    putJM = True -- ("core" `elem` printPass flags || "opt" `elem` printPass flags)
    in when putJM $ TL.IO.hPutStrLn outHandle (prettyJudgedModule putBind renderOpts j)
  unless (outHandle == stdout) (SIO.hClose outHandle)

  when (doCacheCore && not (noCache flags)) (DB.encodeFile resolverCacheFName r *> cacheFile fName j)
  let okMsg = if coreOK then "OK " <> (if raw then "Raw" else "Fused") else "KO"
    in T.IO.putStrLn $ show fName <> " " <> "(" <> show (modIName j) <> ") " <> okMsg
  pure (r , j)

---------------------------------
-- Phase 2: codegen, linking, jit
---------------------------------
--codegen flags input@((resolver , Import bindNames judged) , exts , judgedModule) = let
codegen flags input@(_resolver , jm) = let ssaMod = mkSSAModule jm in do
  when ("ssa" `elem` printPass flags) $ TL.IO.putStrLn (PrettySSA.prettySSAModule PrettySSA.ansiRender ssaMod)
  when ("C"   `elem` printPass flags) $ let str = mkC ssaMod
    in BSL.IO.putStr str *> BSL.IO.putStr "\n" *> BSL.IO.writeFile "/tmp/aryaOut.c" str
  when (interpret flags) (T.IO.putStrLn $ _interpretModule jm)
  pure input

----------
-- Repl --
----------
replWith :: forall a. a -> (a -> Text -> IO a) -> IO a
replWith startState fn = let
  doLine state = getInputLine ", " >>= \case
    Nothing -> pure state
    Just l  -> lift (fn state (toS l)) >>= doLine
  in runInputT defaultSettings $ doLine startState

replCore :: CmdLine -> IO ()
replCore cmdLine = let
  doLineE l = let
    handler caught = defaultRet <$ maybe (pure ()) (\(ErrorCall msg) -> putStrLn msg) (fromException caught)
    defaultRet = (primResolver , emptyJudgedModule)
    in catch (doLine l) handler
  doLine l = text2Core cmdLine Nothing primResolver 0 "<stdin>" l
    >>= putResults . simplifyModule
--  >>= codegen cmdLine
--  >>= print . V.last . allBinds . fst
  in void $ replWith cmdLine $ \cmdLine line -> cmdLine <$ doLineE line
