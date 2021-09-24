{-# LANGUAGE OverloadedStrings #-}
-- llvm driver
-- * AST.Module -> LLVM.Module (haskell to c++)
-- * optimizing modules
-- * jit
-- * linking and producing executables
module LlvmDriver
where
{-

import qualified Data.ByteString.Short as BS

import qualified LLVM.AST
import qualified LLVM.Module
import LLVM.Context
import LLVM.PassManager
--import LLVM.Transforms
import LLVM.Analysis
--import LLVM.Pretty (ppllvm)
import qualified Data.ByteString.Char8 as B

--JIT
import LLVM.Target
--import LLVM.CodeModel
import LLVM.Relocation as Reloc
import qualified LLVM.ExecutionEngine as EE
import Foreign.Ptr -- for fn pointers in the JIT

import LLVM.OrcJIT
import LLVM.CodeGenOpt as CodeGenOpt
import LLVM.CodeModel as CodeModel
import LLVM.Internal.OrcJIT.CompileLayer
import LLVM.Linking

foreign import ccall "dynamic" haskFun :: FunPtr (IO Double) -> IO Double

type ModuleAST = LLVM.AST.Module    -- haskell llvm-hs-pure
type ModuleCPP = LLVM.Module.Module -- c++ version

 -- llvmpretty: maybe remove this dependency, it's not super helpful, although
 -- it helped in one case since the output is slightly different to llvm disassembler.
dumpModule :: ModuleAST -> IO () = \m ->
  withCppModule m ((B.putStrLn =<<) . LLVM.Module.moduleLLVMAssembly)

withCppModule :: ModuleAST -> (ModuleCPP -> IO a) -> IO a 
withCppModule m go =
 let action m = verify m *> go m 
 in withContext $ \c -> LLVM.Module.withModuleFromAST c m action

optimize :: ModuleCPP -> (ModuleCPP -> IO a) -> IO a
optimize m f = withPassManager defaultPassSetSpec $ \pm ->
  runPassManager pm m *> f m
-- eg. withCppModule moduleAST $ optimize f

writeFile :: FilePath -> ModuleAST -> IO () = \fNm mod ->
  withHostTargetMachineDefault $ \tm -> do
  dataLayout <- getTargetMachineDataLayout tm
  withCppModule mod{LLVM.AST.moduleDataLayout=Just dataLayout}
    (go fNm tm)
  where
  bc  tm = LLVM.Module.writeBitcodeToFile
  obj tm = LLVM.Module.writeObjectToFile tm
  go fNm tm mod = bc tm (LLVM.Module.File fNm) mod

passes :: Word -> PassSetSpec = \opt -> defaultCuratedPassSetSpec
  { optLevel = if opt>0 then Just opt else Nothing } -- otherwise SEGV lol

---------
-- JIT --
---------
-- since the only way to get llvm modules is via 'withModule*' style functions,
-- this fns' implementation is necessarily weird
-- note LLVM.Module.linkModules moves the second (destroyed) into the first.
withLinkedModules :: [ModuleAST] -> (Context -> ModuleCPP -> IO a)->IO a
withLinkedModules ms go = withContext $ \c ->
  LLVM.Module.withModuleFromBitcode c (LLVM.Module.File "Memory/hack.bc") $ \hack ->
  let withMod m action = LLVM.Module.withModuleFromAST c m (action c)
  in case ms of
  []   -> error "no module"
--[m]  -> withMod m go
  [m]  -> withMod m $ \c1 m1 -> LLVM.Module.linkModules m1 hack *> go c1 m1
  m:ms -> withMod m $ \c1 m1 -> withLinkedModules ms $ \c1 m2 ->
    LLVM.Module.linkModules m1 m2 *> go c m1

-- run an extern function TODO elaborate..
runExtern :: FunPtr a -> IO Double -- why double.. ?
runExtern fn = haskFun (castFunPtr fn :: FunPtr (IO Double))

runJIT :: Word -> [ModuleAST] -> ModuleAST -> IO ()
runJIT opt objs mod =
  let runFn fnName engine m = EE.withModuleInEngine engine m $ \ee -> do
          EE.getFunction ee (LLVM.AST.mkName fnName) >>= \case
            Nothing -> pure Nothing
            Just fn -> runExtern fn >>= pure . Just
      -- jit options
      opt     = Just 0
      model   = Nothing
      ptrelim = Nothing
      fastins = Nothing
  in
  withLinkedModules (mod : objs) $ \context m ->
  EE.withMCJIT context opt model ptrelim fastins $ \ executionEngine ->
--  withContext $ \context ->
--  EE.withMCJIT context opt model ptrelim fastins $ \ executionEngine ->
--  LLVM.Module.withModuleFromAST context mod $ \m ->
    verify m -- llvm sanity check
    *> runFn "main" executionEngine m >>= \case
        Nothing -> error "main() not found"
        Just r  -> pure ()

--newtype JITMachine b = JITMachine { jitmachine :: (ModuleAST , BS.ShortByteString , FunPtr b -> IO ()) -> IO (JITMachine b) }
data JITState = JITState {
   jitContext :: Context
 , jitES :: ExecutionSession
 , jitTM :: TargetMachine
 , jitcompileLayer :: IRCompileLayer ObjectLinkingLayer
}

withJITMachine go = let
  -- the jit needs a (module -> symbol) resolver to find symbols during the linking/compile stage
  myResolver = SymbolResolver $ \mangled -> getSymbolAddressInProcess mangled >>= \ptr -> pure $
    Right (JITSymbol ptr (defaultJITSymbolFlags { jitSymbolExported = True }))
  myResolver2 ircl = SymbolResolver $ \mangled -> findSymbol ircl mangled False >>= \case
    s@Right{} -> pure s
    Left{}    -> getSymbolAddressInProcess mangled >>= \ptr -> pure $ Right $ (JITSymbol ptr (defaultJITSymbolFlags { jitSymbolExported = True }))
  in
  withContext $ \context ->
  (loadLibraryPermanently Nothing *>) $ -- load symbols from current process (basically libc)
  withHostTargetMachine Reloc.PIC CodeModel.Default CodeGenOpt.Default $ \tm ->
  withExecutionSession $ \es ->
  withSymbolResolver es myResolver $ \psr ->
  withObjectLinkingLayer es (\k -> pure psr  {- fmap (\rs -> rs Map.! k  ) (readIORef resolvers)-}) $ \objectLayer ->
  withIRCompileLayer objectLayer tm $ \compileLayer ->

  LLVM.Module.withModuleFromBitcode context (LLVM.Module.File "Memory/hack.bc") $ \hack ->
  withModuleKey es $ \k -> addModule compileLayer k hack *>
  go (JITState context es tm compileLayer)

runINJIT :: JITState -> (ModuleAST , BS.ShortByteString , (FunPtr b -> IO ())) -> IO ()
runINJIT (JITState context es tm compileLayer) (hsMod , nm , doFn) =
    LLVM.Module.withModuleFromAST context hsMod $ \cppMod -> do
    -- Note addModule destroys the module, mergeing it into the jit
    withModuleKey es $ \k -> addModule compileLayer k cppMod
    fSymbol <- mangleSymbol compileLayer nm
    findSymbol compileLayer fSymbol True >>= \case
      Left{} -> putStrLn ("Couldn't find: " ++ show nm)
      Right (JITSymbol fnAddr _) -> do
        let fn = castPtrToFunPtr (wordPtrToPtr fnAddr)
        doFn fn
--      mkMainFun fn
        runExtIOFn compileLayer "flushStdout"
--      evaluate $ DeepSeq.force (mkMainFun fn)
--      print $ mkDoubleFun fn $ 3.3
    pure ()

runExtIOFn compileLayer name = mangleSymbol compileLayer name >>= \nm' -> findSymbol compileLayer nm' True >>= \case
  Right (JITSymbol fflush _) -> mkMainFun (castPtrToFunPtr (wordPtrToPtr fflush))
  Left{} -> putStrLn $ "couldn't find symbol" ++ show name

-- mkDoubleFun :: FunPtr (Double -> Double) -> (Double -> Double)

foreign import ccall "dynamic"
  mkDoubleFun :: FunPtr (Double -> Double) -> (Double -> Double)
foreign import ccall "dynamic"
  mkMainFun :: FunPtr (IO ()) -> (IO ())

testJIT = withJITMachine $ \jit -> do
  runINJIT jit (LLVM.AST.defaultModule , "test" , \f -> (mkMainFun f))
  runINJIT jit (LLVM.AST.defaultModule , "xd" , \f -> print $ (mkDoubleFun f) 3.3)
--  >>= \js -> incrementalJIT (Just js) (LLVM.AST.defaultModule , "test" , \f -> pure ())
-}
