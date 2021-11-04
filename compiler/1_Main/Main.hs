-- main = Text >> Parse >> Core >> STG >> LLVM
import CmdLine
import qualified ParseSyntax as P
import Parser
import ModulePaths
import Externs
import CoreSyn
import CoreBinary()
import CoreUtils (bind2Expr)
import PrettyCore
import Infer
import Eval
import MkSSA
import C

import Text.Megaparsec hiding (many)
import qualified Data.Text.IO as T.IO
import qualified Data.ByteString.Lazy as BSL.IO
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Binary as DB
import Control.Lens
import System.Console.Haskeline
import System.Directory
import Data.List (words)

searchPath   = ["./" , "Library/"]
objPath      = ["./"]
objDir       = ".irie-obj/@" -- prefix '@' to files in there
getCachePath fName = objDir <> map (\case { '/' -> '%' ; x -> x} ) fName
resolverCacheFName = getCachePath "resolver"
doCacheCore  = True

deriving instance Generic GlobalResolver
deriving instance Generic Externs
instance DB.Binary GlobalResolver
instance DB.Binary Externs

-- for use in ghci
demoFile   = "demo.ii"
sh         = main' . Data.List.words
shL        = main' . (["-p" , "llvm-hs"] ++ ) . Data.List.words
parseTree  = sh $ demoFile <> " -p parse"
ssa        = sh $ demoFile <> " -p ssa"
core       = sh $ demoFile <> " -p core"
types      = sh $ demoFile <> " -p types"
opt        = sh $ demoFile <> " -p simple"
emitC      = sh $ demoFile <> " -p C"

main = getArgs >>= main'
main' args = parseCmdLine args >>= \cmdLine ->
  when ("args" `elem` printPass cmdLine) (print cmdLine)
  *> case files cmdLine of
    []  -> replCore cmdLine
    av  -> do
      exists   <- doesFileExist resolverCacheFName
      resolver <- if doCacheCore && exists
        then DB.decodeFile resolverCacheFName :: IO GlobalResolver
        else pure primResolver
      av `forM_` doFileCached cmdLine True resolver

--doFile cmdLine r f     = T.IO.readFile f >>= doProgText cmdLine r f
doProgText flags r f t = text2Core flags Nothing r f t >>= codegen flags

type CachedData = (ModuleIName , Externs , JudgedModule)
decodeCoreFile :: FilePath -> IO CachedData       = DB.decodeFile
encodeCoreFile :: FilePath -> CachedData -> IO () = DB.encodeFile
cacheFile fp jb = createDirectoryIfMissing False objDir *> encodeCoreFile (getCachePath fp) jb

doFileCached :: CmdLine -> Bool -> GlobalResolver -> FilePath -> IO (GlobalResolver , Externs , JudgedModule)
doFileCached flags isMain resolver fName = let
  cached            = getCachePath fName
  isCachedFileFresh = (<) <$> getModificationTime fName <*> getModificationTime cached
  go resolver modNm = T.IO.readFile fName >>= text2Core flags modNm resolver fName
  go' resolver = go resolver Nothing
  in
  if not doCacheCore then go' resolver else doesFileExist cached >>= \exists ->
  if not exists      then go' resolver else do
    fresh <- isCachedFileFresh
    -- TODO don't read everything if wasn't fresh
    last@(modINm , exts , judged) <- decodeCoreFile cached :: IO CachedData
    -- need to clear all cached bindings in case some were removed since
    if fresh && not (recompile flags) && not isMain then pure (resolver , exts , judged)
      --else go (rmModule modINm (bindNames judged) resolver) (Just modINm)
      else go resolver (Just $ OldCachedModule modINm (bindNames judged))

evalImports flags resolver fileNames = do
  importPaths <- (findModule searchPath . toS) `mapM` fileNames
  -- import loop?
  foldM (\res path -> (\(a,b,c)->a) <$> doFileCached flags False res path) resolver importPaths

-- Just moduleIName indicates this module was already cached, so don't allocate a new iname for it
text2Core :: CmdLine -> Maybe OldCachedModule -> GlobalResolver -> FilePath -> Text
  -> IO (GlobalResolver , Externs , JudgedModule)
text2Core flags maybeOldModule resolver fName progText = do
  when ("source" `elem` printPass flags) (putStr =<< readFile fName)
  parsed <- case parseModule fName progText of
    Left e  -> (putStrLn $ errorBundlePretty e) *> die ""
    Right r -> pure r
  when ("parseTree" `elem` printPass flags) (putStrLn (P.prettyModule parsed) <* die "")

  modResolver <- evalImports flags resolver (parsed ^. P.imports)

  let modNameMap = parsed ^. P.parseDetails . P.hNameBinds . _2
      hNames = let getNm (P.FunBind fnDef) = P.fnNm fnDef
        in getNm <$> V.fromList (parsed ^. P.bindings)
      nBinds       = length $ parsed ^. P.bindings
      localNames   = parsed ^. P.parseDetails . P.hNameBinds   . _2
      mixfixNames  = parsed ^. P.parseDetails . P.hNameMFWords . _2
      unknownNames = parsed ^. P.parseDetails . P.hNamesNoScope
      labelMap     = parsed ^. P.parseDetails . P.labels
      labelNames   = iMap2Vector $ parsed ^. P.parseDetails . P.labels
      fieldNames   = iMap2Vector $ parsed ^. P.parseDetails . P.fields
      nArgs        = parsed ^. P.parseDetails . P.nArgs
      srcInfo = Just (SrcInfo progText (VU.reverse $ VU.fromList $ parsed ^. P.parseDetails . P.newLines))

      (modIName , isNewModule) = maybe (modCount modResolver , True)
                                       ((,False) . oldModuleIName) maybeOldModule

      (tmpResolver  , exts) = resolveImports modResolver localNames labelMap mixfixNames unknownNames maybeOldModule

      (judgedModule , errors) = judgeModule nBinds parsed modIName nArgs hNames exts srcInfo
      TCErrors scopeErrors biunifyErrors checkErrors = errors
      JudgedModule modNm nArgs' bindNames a b judgedBinds = judgedModule

      newResolver = let
        labelExprs  = let
          mkLabelExpr iName = Core (CoreSyn.Label (mkQName modIName iName) []) []
          in V.fromList (mkLabelExpr <$> [nBinds .. nBinds + V.length labelNames - 1])

        -- add labelNames and dummy bindings so they can be imported by other modules
        -- necessary to disambiguate (Cons a b) (label or not-in-scope?)
        -- case on labels and all uses of fields are unambiguous
        r = addModule2Resolver tmpResolver (V.zip (bindNames V.++ labelNames) ((bind2Expr <$> judgedBinds) V.++ labelExprs))
        in r { lnames   = lnames r `V.snoc` labelNames 
             , fnames   = fnames r `V.snoc` fieldNames 
             , modCount = modCount r + (if isNewModule then 1 else 0) }

      bindNamePairs = V.zip bindNames judgedBinds
      bindSrc = BindSource _ bindNames _ (lnames newResolver) (fnames newResolver) (allBinds newResolver)
      namedBinds showBind bs = (\(nm,j)->clYellow nm <> toS (prettyBind showBind bindSrc j)) <$> bs
--traceShowM (fName , maybeOldModule , modIName)

  when ("types"  `elem` printPass flags) (void $ T.IO.putStrLn `mapM` namedBinds False bindNamePairs)
  when ("core"   `elem` printPass flags) (void $ T.IO.putStrLn `mapM` namedBinds True  bindNamePairs)
  let simpleBinds = runST $ V.thaw judgedBinds >>= \cb ->
          simplifyBindings nArgs (V.length judgedBinds) cb *> V.unsafeFreeze cb
      coreOK = null biunifyErrors && null scopeErrors && null checkErrors
      judgedFinal = JudgedModule modNm nArgs bindNames a b simpleBinds
  when ("simple" `elem` printPass flags)
    (void $ T.IO.putStrLn `mapM` namedBinds True  (V.zip bindNames simpleBinds))
  (T.IO.putStrLn . formatError bindSrc srcInfo) `mapM` biunifyErrors
  (T.IO.putStrLn . formatScopeError)            `mapM` scopeErrors
  (T.IO.putStrLn . formatCheckError bindSrc)    `mapM` checkErrors
  when (doCacheCore && coreOK && not (noCache flags)) $ do
    DB.encodeFile resolverCacheFName newResolver
    cacheFile fName (modIName , exts , judgedFinal)
  traceM $ show fName <> " " <> (if coreOK then clGreen "OK" else clRed "KO")
  pure (newResolver , exts , judgedFinal)

---------------------------------
-- Phase 2: codegen, linking, jit
---------------------------------
--codegen flags input@((resolver , Import bindNames judged) , exts , judgedModule) = let
codegen flags input@(resolver , exts , jm@(JudgedModule modNm nArgs bindNms a b judgedBinds)) = let
  ssaMod = mkSSAModule exts (JudgedModule modNm nArgs bindNms a b judgedBinds)
  in do
    when ("ssa" `elem` printPass flags) $ T.IO.putStrLn (show ssaMod)
    when ("C"   `elem` printPass flags) $ let str = mkC ssaMod
      in BSL.IO.putStrLn str *> BSL.IO.writeFile "/tmp/aryaOut.c" str
    pure input
--llvmMod      = mkStg exts (JudgedModule modNm bindNms a b judgedBinds)
--putPass :: Text -> IO () = \case
--  "llvm-hs"    -> let
--    text = ppllvm llvmMod
--    in TL.IO.putStrLn text *> TL.IO.writeFile "/tmp/aryaOut.ll" text
--  "llvm-cpp"   -> LD.dumpModule llvmMod
--  _            -> pure ()
--in input <$ do
--  putPass `mapM_` printPass flags
--  when (jit flags) $ LD.runJIT (optlevel flags) [] llvmMod

----------
-- Repl --
----------
replWith :: forall a. a -> (a -> Text -> IO a) -> IO a
replWith startState fn = let
  doLine state = getInputLine "$ " >>= \case
    Nothing -> pure state
    Just l  -> lift (fn state (toS l)) >>= doLine
  in runInputT defaultSettings $ doLine startState

replCore :: CmdLine -> IO ()
replCore cmdLine = let
  doLine l = doProgText cmdLine primResolver "<stdin>" l >>= print . V.last . allBinds . (\(a,b,c) -> a)
  in void $ replWith cmdLine $ \cmdLine line -> cmdLine <$ doLine line

--replJIT :: CmdLine -> IO ()
--replJIT cmdLine = LD.withJITMachine $
--  \jit -> void $ replWith (cmdLine , jit) $
--  \state@(cmdLine , jit) l -> do
--    judged@((_,Import _ j),exts,jm) <- doProgText cmdLine primResolver "<stdin>" l
--    print $ importBinds $ snd $ (\(a,b,c)->a) judged
--    let llMod = mkStg exts (fst<$>j) jm
--    LD.runINJIT jit (Just (llMod , "test" , \_ -> pure ()))
--    pure state

repl2 = mapM T.IO.putStrLn =<< replWith [] (\st line -> pure $! line : st)

testrepl = replCore defaultCmdLine

--testjit = LD.testJIT
