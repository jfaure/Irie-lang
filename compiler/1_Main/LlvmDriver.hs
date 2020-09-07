-- llvm driver
-- * AST.Module -> LLVM.Module (haskell to c++)
-- * optimizing modules
-- * jit
-- * linking and producing executables
module LlvmDriver
where
{-# LANGUAGE OverloadedStrings #-}

import Control.Monad
import qualified LLVM.AST
import qualified LLVM.Module
import LLVM.Context
import LLVM.PassManager
import LLVM.Transforms
import LLVM.Analysis
--import LLVM.Pretty (ppllvm)
import qualified Data.ByteString.Char8 as B

--JIT
--import Data.Word
import LLVM.Target
import LLVM.CodeModel
import qualified LLVM.ExecutionEngine as EE
import Foreign.Ptr ( FunPtr, castFunPtr ) -- pointer to functions in the JIT
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
-- note LLVM.Module.linkModules destroys the second module
withLinkedModules :: [ModuleAST] -> (Context -> ModuleCPP -> IO a)->IO a
withLinkedModules ms go = withContext $ \c -> 
  let withMod m action = LLVM.Module.withModuleFromAST c m (action c)
  in case ms of
  []   -> error "no module"
  [m]  -> withMod m go
  m:ms -> withMod m $ \c1 m1 -> withLinkedModules ms $ \c2 m2 ->
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
  
