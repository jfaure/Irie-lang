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
--import qualified Data.Text.Lazy.IO as TL.IO
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
      doFile cmdLine resolver `mapM_` av

doFile cmdLine r f     = T.IO.readFile f >>= doProgText cmdLine r f
doProgText flags r f t = text2Core flags r f t >>= codegen flags

type CachedData = (GlobalResolver , Externs , JudgedModule)
decodeCoreFile :: FilePath -> IO CachedData       = DB.decodeFile
encodeCoreFile :: FilePath -> CachedData -> IO () = DB.encodeFile
cacheFile fp jb = createDirectoryIfMissing False objDir *> encodeCoreFile (getCachePath fp) jb

doFileCached :: CmdLine -> GlobalResolver -> FilePath -> IO (GlobalResolver , Externs , JudgedModule)
doFileCached flags resolver fName = let
  cached            = getCachePath fName
  isCachedFileFresh = (<) <$> getModificationTime fName <*> getModificationTime cached
  isCachedFileOK    = doesFileExist cached >>= \exists -> if doCacheCore && exists then isCachedFileFresh else pure False
  in isCachedFileOK >>= \case
  -- Warning ! this will almost certainly not work when varying the import order across caches
  False -> T.IO.readFile fName >>= text2Core flags resolver fName
  True  -> decodeCoreFile cached >>= \(_newResolver , exts , judged) -> do
--  modResolver <- evalImports modResolver localNames mixfixNames unknownNames
    -- TODO modResolver + recompile dependencies ?
--  let (tmpResolver , exts) = resolveImports tmpResolver mempty mempty mempty -- localName smixfixNames unknownNames
--      newResolver = addModule2Resolver tmpResolver (bind2Expr <$> (judgedBinds judged))
    pure (resolver , exts , judged)

evalImports flags resolver fileNames = do
  importPaths <- (findModule searchPath . toS) `mapM` fileNames
  foldM (\res path -> (\(a,b,c)->a) <$> doFileCached flags res path) resolver importPaths

text2Core :: CmdLine -> GlobalResolver -> FilePath -> Text
  -> IO (GlobalResolver , Externs , JudgedModule)
text2Core flags resolver fName progText = do
  when ("source" `elem` printPass flags) (putStr =<< readFile fName)
  parsed <- case parseModule fName progText of
    Left e  -> (putStrLn $ errorBundlePretty e) *> die ""
    Right r -> pure r
  when ("parseTree" `elem` printPass flags) (putStrLn $ P.prettyModule parsed)

  modResolver <- evalImports flags resolver (parsed ^. P.imports)

  let (tmpResolver , exts) = resolveImports modResolver localNames mixfixNames unknownNames
      modIName     = modCount tmpResolver

      modNameMap = parsed ^. P.parseDetails . P.hNameBinds . _2
      hNames = let getNm (P.FunBind fnDef) = P.fnNm fnDef in getNm <$> V.fromList (parsed ^. P.bindings)
      localNames   = parsed ^. P.parseDetails . P.hNameBinds . _2
      mixfixNames  = parsed ^. P.parseDetails . P.hNameMFWords . _2
      unknownNames = parsed ^. P.parseDetails . P.hNamesNoScope
      labelNames   = iMap2Vector $ parsed ^. P.parseDetails . P.labels
      fieldNames   = iMap2Vector $ parsed ^. P.parseDetails . P.fields
      nArgs        = parsed ^. P.parseDetails . P.nArgs
      srcInfo = Just (SrcInfo progText (VU.reverse $ VU.fromList $ parsed ^. P.parseDetails . P.newLines))

      (judgedModule , errors) = judgeModule parsed modIName nArgs hNames exts srcInfo
      TCErrors scopeErrors biunifyErrors = errors
      JudgedModule modNm nArgs' bindNames a b judgedBinds = judgedModule

      newResolver' = addModule2Resolver tmpResolver (V.zip bindNames (bind2Expr <$> judgedBinds))
      newResolver = newResolver' { lnames = lnames newResolver' `V.snoc` labelNames 
                                 , fnames = fnames newResolver' `V.snoc` fieldNames }

      bindNamePairs = V.zip bindNames judgedBinds
      bindSrc = BindSource _ bindNames _ (lnames newResolver) (fnames newResolver) (allBinds newResolver)
      namedBinds showBind bs = (\(nm,j)->clYellow nm <> toS (prettyBind showBind bindSrc j)) <$> bs

  when ("types"  `elem` printPass flags) (void $ T.IO.putStrLn `mapM` namedBinds False bindNamePairs)
  when ("core"   `elem` printPass flags) (void $ T.IO.putStrLn `mapM` namedBinds True  bindNamePairs)
  let simpleBinds = runST $ V.thaw judgedBinds >>= \cb ->
          simplifyBindings nArgs (V.length judgedBinds) cb *> V.unsafeFreeze cb
      coreOK = null biunifyErrors && null scopeErrors
      judgedFinal = JudgedModule modNm nArgs bindNames a b simpleBinds
  when ("simple" `elem` printPass flags)
    (void $ T.IO.putStrLn `mapM` namedBinds True  (V.zip bindNames simpleBinds))
  (T.IO.putStrLn . formatError bindSrc srcInfo)      `mapM` biunifyErrors
  (T.IO.putStrLn . formatScopeError) `mapM` scopeErrors
  when (doCacheCore && coreOK) $ do
    DB.encodeFile resolverCacheFName newResolver
    cacheFile fName (newResolver , exts , judgedFinal)
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
