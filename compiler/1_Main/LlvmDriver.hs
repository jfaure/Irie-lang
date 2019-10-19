-- llvm driver
-- * AST.Module -> LLVM.Module (haskell to c++)
-- * optimizing modules
-- * jit
-- * linking and producing executables
module LlvmDriver
where
{-# LANGUAGE OverloadedStrings #-}

import qualified LLVM.AST
import qualified LLVM.Module
import LLVM.Context
import LLVM.PassManager
import LLVM.Transforms
import LLVM.Analysis
--import LLVM.Pretty (ppllvm)
import qualified Data.Text.IO as T.IO
import qualified Data.ByteString.Char8 as B

--JIT
import Data.Word
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

passes :: Word -> PassSetSpec = \opt -> defaultCuratedPassSetSpec
  { optLevel = if opt>0 then Just opt else Nothing } -- otherwise SEGV lol

---------
-- JIT --
---------
-- run an extern function TODO elaborate.. seems tied to a nonsense signature
runExtern :: FunPtr a -> IO Double -- double.. ?
runExtern fn = haskFun (castFunPtr fn :: FunPtr (IO Double))

runJIT :: Word -> ModuleAST -> IO ()
runJIT opt mod =
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
  withContext $ \context ->
  EE.withMCJIT context opt model ptrelim fastins $ \ executionEngine ->
  LLVM.Module.withModuleFromAST context mod $ \m ->
    verify m -- llvm sanity check
    *> runFn ("main") executionEngine m >>= \case
        Nothing -> error "main() not found"
        Just r  -> pure ()
  
