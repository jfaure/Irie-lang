-- main = Text >> Parse >> Core >> STG >> LLVM
module Main where
import CmdLine
import qualified ParseSyntax as P
import Parser (parseModule)
import ModulePaths (findModule)
import Externs
import CoreSyn ( ModIName, BindSource(BindSource), JudgedModule(JudgedModule, bindNames, labelNames, modIName), OldCachedModule(OldCachedModule, oldModuleIName), SrcInfo(..) )
import Errors
import CoreBinary()
import CoreUtils (bind2Expr)
import PrettyCore ( ansiRender, prettyBind, RenderOptions(ansiColor, bindSource) )
import qualified PrettySSA
import Infer (judgeModule)
import Fuse (simplifyBindings)
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

searchPath   = ["./" , "imports/"]
objPath      = ["./"]
objDir'      = ".irie-obj/"
objDir       = objDir' <> "@" -- prefix '@' to files in there
getCachePath fName = let
  -- ./module == module for cache purposes so they must be converted
  normalise fName = case fName of
    '.' : '/' : _ → fName
    '/' : _ → fName
    _ → '.' : '/' : fName
  in objDir <> map (\case { '/' → '%' ; x → x} ) (normalise fName)
resolverCacheFName = getCachePath "resolver"
doCacheCore  = True
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
shL        = main' . (["-p" , "llvm-hs"] ++ ) . Data.List.words
parseTree  = sh $ demoFile <> " -p parse"
ssa        = sh $ demoFile <> " -p ssa"
core       = sh $ demoFile <> " -p core"
types      = sh $ demoFile <> " -p types"
opt        = sh $ demoFile <> " -p simple"
emitC      = sh $ demoFile <> " -p C"
testRepl   = sh ""

main = getArgs ≫= main'
main' args = parseCmdLine args ≫= \cmdLine → do
  when ("args" `elem` printPass cmdLine) (print cmdLine)
  when doCacheCore (createDirectoryIfMissing False objDir')
  resolverExists ← doesFileExist resolverCacheFName
  resolver       ← if doCacheCore && not (noCache cmdLine) && resolverExists
    then DB.decodeFile resolverCacheFName ∷ IO GlobalResolver
    else pure primResolver
  unless (null (strings cmdLine)) $ [strings cmdLine] `forM_` \e →
    text2Core cmdLine Nothing resolver 0 "CmdLineBindings" (toS e)
      ≫= putResults . handleJudgedModule
      ≫= codegen cmdLine
  files cmdLine `forM_` doFileCached cmdLine True resolver 0
  when (repl cmdLine || (null (files cmdLine) && null (strings cmdLine))) $ let
    patchFlags = cmdLine{ printPass = "types" : printPass cmdLine , repl = True , noColor = False }
    in replCore (if null (printPass cmdLine) then patchFlags else cmdLine)

type CachedData = JudgedModule
decodeCoreFile ∷ FilePath → IO CachedData       = DB.decodeFile
encodeCoreFile ∷ FilePath → CachedData → IO () = DB.encodeFile
cacheFile fp jb = createDirectoryIfMissing False objDir *> encodeCoreFile (getCachePath fp) jb

doFileCached ∷ CmdLine → Bool → GlobalResolver → ModDeps → FilePath → IO (GlobalResolver , JudgedModule)
doFileCached flags isMain resolver depStack fName = let
  cached            = getCachePath fName
  isCachedFileFresh = (<) <$> getModificationTime fName <*> getModificationTime cached
  go resolver modNm = T.IO.readFile fName
    ≫= text2Core flags modNm resolver depStack fName
    ≫= putResults . handleJudgedModule
    ≫= codegen flags
  go' resolver = go resolver Nothing
  didIt = modNameMap resolver M.!? toS fName
  in case didIt of
    Just _    | not doCacheCore || noCache flags → error $ "compiling a module twice without cache is unsupported: " <> show fName
    Just modI | depStack `testBit` modI → error $ "Import loop: "
      <> toS (T.intercalate " ← " (show . (modNamesV resolver V.!) <$> bitSet2IntList depStack))
    _         | not doCacheCore → go' resolver
    _ → doesFileExist cached ≫= \exists → if not exists then go' resolver else do
      fresh  ← isCachedFileFresh
      judged ← decodeCoreFile cached ∷ IO CachedData -- even stale cached modules need to be read
      if fresh && not (recompile flags) && not isMain then pure (resolver , judged)
        --else go (rmModule modINm (bindNames judged) resolver) (Just modINm)
        else go resolver (Just $ OldCachedModule (modIName judged) (bindNames judged <> V.fromList (M.keys (labelNames judged))))

evalImports ∷ CmdLine → ModIName → GlobalResolver → BitSet → [Text] → IO (Bool, GlobalResolver, ModDependencies)
evalImports flags moduleIName resolver depStack fileNames = do
  (nopath , importPaths) ← partitionEithers <$> (findModule searchPath . toS) `mapM` fileNames
  nopath `forM_` \f → putStrLn $ ("couldn't find " <> show f <> " in search path\n" <> show searchPath ∷ Text)

  -- the compilation work stack is the same for each imported module
  -- TODO this foldM could be parallel
  (r , importINames) ← let
    inferImport (res,imports) path = (\(a,j)→(a,modIName j: imports)) <$> doFileCached flags False res depStack path
    in foldM inferImport (resolver , []) importPaths
  let modDeps = ModDependencies { deps = foldl setBit emptyBitSet importINames , dependents = emptyBitSet }
      r' = foldl (\r imported → addDependency imported moduleIName r) r importINames
  pure (null nopath , r' , modDeps)

-- Parse , judge , simplify a module (depending on cmdline flags)
--text2Core ∷ CmdLine → Maybe OldCachedModule → GlobalResolver → ModDeps → FilePath → Text
--  → IO (CmdLine, [Char], JudgedModule, GlobalResolver, Externs , Errors , Maybe SrcInfo)
text2Core flags maybeOldModule resolver' depStack fName progText = do
  -- Just moduleIName indicates this module was already cached, so don't allocate a new module iname for it
  let modIName = maybe (modCount resolver') oldModuleIName maybeOldModule
      resolver = if isJust maybeOldModule then resolver' else addModName modIName (T.pack fName) resolver'
  when ("source" `elem` printPass flags) (putStr =≪ readFile fName)
  parsed ← case parseModule fName progText of
    Left e  → putStrLn (errorBundlePretty e) $> P.emptyParsedModule (toS fName) -- TODO add to parse fails
    Right r → pure r
  when ("parseTree" `elem` printPass flags) (putStrLn (P.prettyModule parsed))

  (importsok , modResolver , modDeps) ← evalImports flags modIName resolver (setBit depStack modIName) (parsed ^. P.imports)
  pure $ inferResolve flags fName modIName modResolver modDeps parsed progText maybeOldModule

-- Judge the module and update the global resolver
inferResolve ∷ CmdLine → [Char] → Int → GlobalResolver → ModDependencies → P.Module → Text → Maybe OldCachedModule
  → (CmdLine , [Char] , JudgedModule , GlobalResolver , Externs , Errors , Maybe SrcInfo)
inferResolve flags fName modIName modResolver modDeps parsed progText maybeOldModule = let
  nBinds      = length $ parsed ^. P.bindings
  hNames      = P.fnNm <$> V.fromListN nBinds (parsed ^. P.bindings)
  labelMap    = parsed ^. P.parseDetails . P.labels
  fieldMap    = parsed ^. P.parseDetails . P.fields
  labelNames  = iMap2Vector labelMap
  nArgs       = parsed ^. P.parseDetails . P.nArgs
  srcInfo     = Just (SrcInfo progText (VU.reverse $ VU.fromList $ parsed ^. P.parseDetails . P.newLines))

  (tmpResolver  , exts) = resolveImports
    modResolver modIName
    (parsed ^. P.parseDetails . P.hNameBinds . _2)   -- local names
    (labelMap , fieldMap)                            -- HName → label and field names maps
    (parsed ^. P.parseDetails . P.hNameMFWords . _2) -- mixfix names
    (parsed ^. P.parseDetails . P.hNamesNoScope)     -- unknownNames not in local scope
    maybeOldModule
  (judgedModule , errors) = judgeModule nBinds parsed (deps modDeps) modIName nArgs hNames exts srcInfo
  JudgedModule _modIName _modNm _nArgs bindNames _a _b judgedBinds = judgedModule

  newResolver = addModule2Resolver tmpResolver modIName
    (V.zip bindNames (bind2Expr <$> judgedBinds)) labelNames (iMap2Vector fieldMap) labelMap fieldMap modDeps
  in (flags , fName , judgedModule , newResolver , exts , errors , srcInfo)

handleJudgedModule ∷ (CmdLine, f, JudgedModule, GlobalResolver, e1, Errors, e2)
  → ( CmdLine, Bool, Errors, BindSource, e2, f, GlobalResolver, JudgedModule
     , (Maybe (V.Vector TL.Text), Maybe (V.Vector TL.Text), Maybe (V.Vector TL.Text)))
handleJudgedModule (flags , fName , judgedModule , newResolver , _exts , errors , srcInfo) = let
  JudgedModule modI modNm nArgs bindNames a b judgedBinds = judgedModule
  nameBinds showTerm bs = let
    prettyBind' = prettyBind ansiRender { bindSource = Just bindSrc , ansiColor = not (noColor flags) }
--  in (\(nm,j) → (prettyBind' showTerm nm j)) <$> bs
    in uncurry (prettyBind' showTerm) <$> bs
  bindNamePairs = V.zip bindNames judgedBinds
  bindSrc = BindSource _ bindNames _ (labelHNames newResolver) (fieldHNames newResolver) (allBinds newResolver)
  coreOK = null (errors ^. biFails) && null (errors ^. scopeFails)
    && null (errors ^. checkFails) && null (errors ^. typeAppFails)
  simpleBinds = runST $ V.unsafeThaw judgedBinds ≫= \cb →
      simplifyBindings modI nArgs (V.length judgedBinds) cb *> V.unsafeFreeze cb
  judgedFinal = JudgedModule modI modNm nArgs bindNames a b (if noFuse flags then judgedBinds else simpleBinds)

  testPass p = coreOK && p `elem` printPass flags && not (quiet flags)
  oTypes  = if testPass "types"  then Just $ nameBinds False bindNamePairs else Nothing
  oCore   = if testPass "core"   then Just $ nameBinds True  bindNamePairs else Nothing
  oSimple = if testPass "simple" then Just $ nameBinds True  (V.zip bindNames simpleBinds) else Nothing
  in (flags , coreOK , errors , bindSrc , srcInfo , fName , newResolver , judgedFinal , (oTypes , oCore , oSimple))

putResults (flags , coreOK , errors , bindSrc , srcInfo , fName , r , j , (oTypes , oCore , oSimple)) = let
  handleErrors h = do
    T.IO.hPutStr  h $ T.concat  $ (<> "\n\n") . formatError bindSrc srcInfo <$> (errors ^. biFails)
    T.IO.hPutStr  h $ T.concat  $ (<> "\n\n") . formatScopeError            <$> (errors ^. scopeFails)
    TL.IO.hPutStr h $ TL.concat $ (<> "\n\n") . formatCheckError bindSrc    <$> (errors ^. checkFails)
    TL.IO.hPutStr h $ TL.concat $ (<> "\n\n") . formatTypeAppError          <$> (errors ^. typeAppFails)
  in do
  -- write to stdout unless an outfile was specified
  outHandle ← case flags.outFile of
    Nothing → pure stdout
    Just fName → openFile fName WriteMode

  handleErrors outHandle

  -- half-compiled modules `not coreOK` should also be cached (since their names were pre-added to the resolver)
  maybe (pure ()) (TL.IO.hPutStrLn outHandle `mapM_`) oCore
  maybe (pure ()) (TL.IO.hPutStrLn outHandle `mapM_`) oTypes
  maybe (pure ()) (TL.IO.hPutStrLn outHandle `mapM_`) oSimple
  unless (outHandle == stdout) (SIO.hClose outHandle)
  when (doCacheCore && not (noCache flags))
    $ DB.encodeFile resolverCacheFName r *> cacheFile fName j
  unless (repl flags) $ let
    okMsg = if coreOK then "OK" <> (if isJust oSimple then " Simplified" else " Raw") else "KO"
    in T.IO.putStrLn $ show fName <> " " <> "(" <> show (modIName j) <> ") " <>  okMsg
  pure (r , j)

---------------------------------
-- Phase 2: codegen, linking, jit
---------------------------------
--codegen flags input@((resolver , Import bindNames judged) , exts , judgedModule) = let
codegen flags input@(_resolver , jm) = let
  ssaMod = mkSSAModule jm
  in do
    when ("ssa" `elem` printPass flags) $ TL.IO.putStrLn (PrettySSA.prettySSAModule PrettySSA.ansiRender ssaMod)
    when ("C"   `elem` printPass flags) $ let str = mkC ssaMod
      in BSL.IO.putStr str *> BSL.IO.putStr "\n" *> BSL.IO.writeFile "/tmp/aryaOut.c" str
    pure input

----------
-- Repl --
----------
replWith ∷ forall a. a → (a → Text → IO a) → IO a
replWith startState fn = let
  doLine state = getInputLine "$ " ≫= \case
    Nothing → pure state
    Just l  → lift (fn state (toS l)) ≫= doLine
  in runInputT defaultSettings $ doLine startState

replCore ∷ CmdLine → IO ()
replCore cmdLine = let
  doLine l = text2Core cmdLine Nothing primResolver 0 "<stdin>" l
    ≫= putResults . handleJudgedModule
--  ≫= codegen cmdLine
--  ≫= print . V.last . allBinds . fst
  in void $ replWith cmdLine $ \cmdLine line → cmdLine <$ doLine line

--replJIT ∷ CmdLine → IO ()
--replJIT cmdLine = LD.withJITMachine $
--  \jit → void $ replWith (cmdLine , jit) $
--  \state@(cmdLine , jit) l → do
--    judged@((_,Import _ j),exts,jm) ← doProgText cmdLine primResolver "<stdin>" l
--    print $ importBinds $ snd $ (\(a,b,c)→a) judged
--    let llMod = mkStg exts (fst<$>j) jm
--    LD.runINJIT jit (Just (llMod , "test" , \_ → pure ()))
--    pure state

--repl2 = mapM T.IO.putStrLn =≪ replWith [] (\st line → pure $! line : st)

--testjit = LD.testJIT
