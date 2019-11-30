{-# LANGUAGE OverloadedStrings, NoMonomorphismRestriction, StrictData
#-}
module StgToLLVM (stgToIRTop) -- :: [STGTopBinding] -> LLVM.Module
where

-- Local imports
import StgSyn
import CodegenRuntime
import DataToLLVM
import LlvmHsExts (globalStringPtr, constZero, charPtrType, unknownPtrType, sizeof)

-- LLVM
import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction hiding (globalStringPtr)
import LLVM.AST hiding (function)
import LLVM.AST.Type as AST
import qualified LLVM.AST.Float as F
import qualified LLVM.AST.Constant as C
--import qualified LLVM.AST.IntegerPredicate as P
--import qualified LLVM.AST.FloatingPointPredicate as Pf
import LLVM.AST.Global
import LLVM.AST.Linkage
import LLVM.AST.Typed
import LLVM.AST.AddrSpace
import LLVM.AST.Attribute

import Data.List (elemIndex) -- to match deconstruction orders
import qualified Data.Vector as V
import qualified Data.Map.Strict as Map
import Control.Monad.State
import Control.Monad.Fix (MonadFix)
import Data.Functor.Identity (Identity)
import Data.Functor

import Debug.Trace
import Control.Exception (assert)

-- StgToLLVM :: STG continuation passing style -> llvm SSA style
--
-- ! Do not confuse codegen semantics and codegened code semantics !
-- It is difficult to be crystal clear within the comments.
--
-- **********************************************
-- * Operational semantics of generated llvm IR *
-- **********************************************
-- Free variables
-- Only functions (and globals) are legal free variables in llvm, they reside in module scope
-- The module contains a function for all bindings, with the exception of local constants.
-- Stack frames are responsible for making sure these are called at most once.
--
-- Applications 
-- LLVM functions must be saturated when called, partial apps are illegal at this stage
--
-- Case expressions
-- value cases are llvm switch instructions
-- data cases use the fns spawned when data declarations are first encountered.
--
-- Stack Frames ~= function layers
-- A key concept in the execution model
-- 1. responsible for data
-- 2. responsible for let bindings: these are fns that should be called at most once

-- stgToIRTop:  This module's only export
stgToIRTop :: StgModule -> LLVM.AST.Module
stgToIRTop (StgModule stgData typeDefs externs bindings) =
 let
  stgToIRState = StgToIRState
     { bindMap      = Map.empty
     , dataFnsMap   = Map.empty
     , typeMap      = Map.empty
     , tupleMap     = Map.empty
     , stackFrame   = Nothing
     , subData      = False
     }
  rtsExterns =
   [ ("malloc", [IntegerType 32], charPtrType)
   , ("free",   [charPtrType],    VoidType)
   , ("error",  [IntegerType 32, IntegerType 32, charPtrType], VoidType)
   ]

  emitCustomRtsFns = do
     let z = ConstantOperand $ C.Int 32 0
         noMatchFnName = "NoPatternMatchError"
     failStr <- globalStringPtr "No default case alt" "noPatternMsg"
     casePanicFn <- function noMatchFnName [] VoidType $ \[] -> do
         let unCont (Just (ContFn f)) = f
         errFn <- gets (unCont . (Map.!? "error") . bindMap)
         call errFn [(z,[]), (z,[]), (ConstantOperand failStr,[])]
         unreachable
     let contF = ContFn casePanicFn
     modify (\x->x{bindMap=Map.insert noMatchFnName contF (bindMap x)})
     pure casePanicFn

  emitRtsDeclarations = mapM emitExtern rtsExterns
    where
    emitExtern (fname, argTys, retTy) = do
      f <- extern fname argTys retTy
      modify (\x->x{bindMap = Map.insert fname (ContFn f) (bindMap x)})
      pure f

  emitModule :: CodeGenModuleConstraints m => m (V.Vector Operand)
  emitModule
    =  registerBindings bindings -- handle forward references
    *> emitRtsDeclarations       -- ensure always declared
    *> emitCustomRtsFns
    *> modify (\x->x {typeMap=Map.fromList $ V.toList typeDefs})
    *> mapM genConstructor stgData
    *> mapM (\(StgBinding nm rhs) -> fnToLlvm nm rhs) externs
    *> mapM (\(StgBinding nm rhs) -> fnToLlvm nm rhs) bindings

  -- Override buildModuleT to get more control over module parameters
  myBuildModuleT nm =
    let mkModule ds = defaultModule
         { moduleName = nm
         , moduleDefinitions = ds
         , moduleTargetTriple = Just "x86_64-pc-linux-gnu" -- TODO
         }
    in fmap mkModule . execModuleBuilderT emptyModuleBuilder
 in evalState (myBuildModuleT "MainModule" emitModule) stgToIRState

-- suspicious function.. but sometimes a vanilla llvmType/alias is expected
-- eg in an extern declaration we cannot really accept anything more complex (?!)
mkLlvmTy :: (CodeGenModuleConstraints m)
  => StgType -> m LLVM.AST.Type
mkLlvmTy = \case
  StgLlvmType t -> pure t
  StgTypeAlias iden -> gets (aliasToType iden . typeMap) >>= \case
    Nothing -> error ("unknown type alias: " ++ show iden)
    Just ty -> mkLlvmTy ty
  any -> error "expected vanilla llvm type or type alias"

-- Check if a type is stg data, in which case stg has to handle it's memory
isStgData :: CodeGenModuleConstraints m => StgType -> m (Maybe C.Constant)
isStgData (StgTypeAlias iden) = gets ((Map.!? iden) . dataFnsMap)
  >>= \case
    Nothing -> maybe (pure Nothing) isStgData =<<
                 gets (aliasToType iden . typeMap)
    Just datafns -> pure (Just $ staticSize datafns)
isStgData _ = pure Nothing

-- fnToLlvm: Find the type of the function, emit it and hand over to stgToIR for the body
-- This is relatively straightforwards, just remember that functions returning data
-- need an extra parameter: a pointer to (stack) memory they can use,
-- and functions calling these need to pass stack memory (from their frame or a prev one !)
fnToLlvm :: (CodeGenModuleConstraints m)
  => StgId -> StgRhs -> m Operand
-- a global
fnToLlvm iden (StgTopRhs [] [] stgRetType (StgLit (StgConstArg global))) =
  ConstantOperand <$> globalArray iden global
fnToLlvm iden r@(StgTopRhs args argTypes stgRetType body) = mdo
  maybeData <- isStgData stgRetType
  retTy <- getType stgRetType
  params  <- map (, ParameterName "a") <$> mapM getType argTypes

  -- register the fn before codegen in case it refs itself
  case maybeData of
    Just sz ->
     modify (\x->x{dataFnsMap=Map.insert iden (ProxyDataFn sz f) (dataFnsMap x)})
     *> modify (\x->x{bindMap = Map.delete iden (bindMap x)}) -- otherwise inf loop..
    Nothing -> modify (\x->x {bindMap = Map.insert iden (ContFn f) (bindMap x)})

  svState <- get -- function args may squash bindings, so save and restore.
  let getArgBinds llvmArgs = zipWith StgBinding ((\(StgVarArg a) -> a) <$> args)
                                                (StgRhsSsa <$> llvmArgs)
      memParam = (charPtrType, ParameterName "mem")
 -- ~= let args in fnbody
  f <- case maybeData of
        Just _ -> function iden (memParam : params) retTy $ \(mem : llvmArgs) -> do
                    modify (\x->x { stackFrame=Just $ StackFrame (C.Int 32 8) mem []} )
                    ret =<< stgToIR (StgLet (getArgBinds llvmArgs) body)

        Nothing -> function iden params retTy $ \llvmArgs -> do
                     ret =<< stgToIR (StgLet (getArgBinds llvmArgs) body)
  put svState
  pure f
-- StgRhsSsa is used internally for binding fn args, should never appear here
-- externs
fnToLlvm iden (StgRhsSsa ssa)   = error "refusing to generate a function for an ssa binding"
fnToLlvm iden (StgRhsConst ssa) = global iden (LLVM.AST.Typed.typeOf ssa) ssa
-- TODO generate wrapper functions if necessary
fnToLlvm iden (StgPrim prim argTys retTy)    =
  let primFn = ContPrim prim argTys retTy Nothing
  in  modify (\x->x { bindMap = Map.insert iden primFn (bindMap x)})
      *> pure (ConstantOperand C.TokenNone) -- hmm
fnToLlvm iden (StgExt funTy@(FunctionType retTy argTys isVA)) = do
  emitDefn $ GlobalDefinition functionDefaults
    { name        = iden
    , linkage     = External
    , parameters  = ([Parameter ty (mkName "") [] | ty <- argTys], isVA)
    , returnType  = retTy
    }
  let f = ConstantOperand $ C.GlobalReference (ptr funTy) iden
  modify (\x->x { bindMap = Map.insert iden (ContFn f) (bindMap x) })
  pure f

-- let bindings without the 'in expr', doesn't codegen anything
registerBindings :: (MonadState StgToIRState m, Foldable f) => f StgBinding -> m ()
registerBindings bindList =
  let insertfn nm cont = modify (\x->x { bindMap = Map.insert nm cont (bindMap x) })
  in mapM_ (\(StgBinding i rhs) -> insertfn i (ContRhs rhs)) bindList

globalArray :: CodeGenModuleConstraints m => Name -> C.Constant -> m C.Constant
globalArray nm arr@C.Array{} = -- const arrays need to be emmited in global scope
    let ty = LLVM.AST.Typed.typeOf arr
    in do
       emitDefn $ GlobalDefinition globalVariableDefaults
         { name                  = nm
         , LLVM.AST.Global.type' = ty
         , linkage               = Private
         , isConstant            = True
         , initializer           = Just arr
         , unnamedAddr           = Just GlobalAddr
         }
       pure $ C.GetElementPtr True (C.GlobalReference (ptr ty) nm) zz
           where zz = [C.Int 32 0, C.Int 32 0]
globalArray nm notArray = pure notArray

-- ***********************************
-- * StgToIR :: STGExpr -> m Operand *
-- ***********************************
-- StgToIR: Goal is to codegen how to reduce an StgExpr to a value.
stgToIR :: (MonadState StgToIRState m,
           MonadModuleBuilder m, MonadIRBuilder m, MonadFix m)
  => StgExpr -> m Operand

-- StgLet: register the bindings and let the 'expr' codegen them when it needs them.
stgToIR (StgLet bindList expr) =
  registerBindings bindList *> stgToIR expr

-- literals/functions with 0 arity
-- One might assume this is trivial.. but we must:
-- * emit constant arrays as globals
-- * call 0 arity functions (thunks)
-- * (maybe) launch threads for applications
-- * prepare stack memory for args returning data
-- * call destructors for args that aren't returned
stgToIR (StgLit lit) =
 let
  -- some literals are in fact 0 arity functions that must be resolved.
  callIfThunk :: CodeGenIRConstraints m => Operand -> m Operand
  callIfThunk s = case LLVM.AST.Typed.typeOf s of
      FunctionType _ [] _                 -> call s []
      PointerType (FunctionType _ [] _) _ -> call s []
      dont_call                           -> pure s

  handle0Arity :: CodeGenIRConstraints m => StgId -> Symbol -> m Operand
  handle0Arity iden = 
      let 
      -- to pass primitives to functions, you need a function pointer
      wrapPrim p argTys retTy = case p of
        -- TODO more prims
         StgPrim2 op -> do
           a <- fresh
           b <- fresh
           let stgArgs = StgVarArg <$> [a, b]
               expr = StgInstr p stgArgs
               rhs = StgTopRhs stgArgs argTys retTy expr
           f <- fnToLlvm iden rhs
           let cont = ContPrim p argTys retTy (Just f)
           modify (\x->x {bindMap = Map.insert iden cont (bindMap x)})
           pure f
         _ -> error $ "internal: no support for wrapping: " ++ show p
      in \case
      ContLi s  -> pure s --  never call literals
      ContFn v  -> callIfThunk v
      ContRhs (StgRhsSsa val) -> pure val -- don't make a function for literals
      ContRhs (StgPrim p argTys retTy) -> wrapPrim p argTys retTy
      ContRhs r -> fnToLlvm iden r >>= callIfThunk -- rly
      ContPrim p argTys retTy fn -> case fn of
       Just f -> pure f
       Nothing -> wrapPrim p argTys retTy
 in case lit of
   StgConstArg l -> pure $ ConstantOperand l -- fresh >>= \nm -> ConstantOperand <$> globalArray nm l
   StgSsaArg s   -> pure s
   -- some varArgs are constructors or lazy closures that we must resolve (call) now.
   StgVarArg i   ->  gets ((Map.!? i) . bindMap) >>= \case
       Just v -> handle0Arity i v
       Nothing -> trace ("suspicious: " ++ show i) $ stgToIR (StgApp i [])
    -- Nothing -> stgConApp i []
    -- Nothing -> error (show i ++ ": variable not found in bindMap")
   StgExprArg e  -> stgToIR e

stgToIR (StgInstr stgPrim args) =
  let mkLlvmInt = ConstantOperand . C.Int 32
      loadVal ptr i =
        let idxs = [mkLlvmInt 0, mkLlvmInt $ fromIntegral i]
        in gep ptr idxs >>= (`load` 0)
  in case stgPrim of
  StgExtractVal i -> mapM (stgToIR . StgLit) args >>= \case
    [arg] -> loadVal arg i
    args -> error "internal error, too many args for StgInstr"
  StgPAp -> stgMkTuple args
  StgPApApp papArity -> mapM (stgToIR . StgLit) args >>= \case
    pap : llArgs -> mapM (loadVal pap) [0..1+papArity] >>= \case
      fn : papArgs -> do
        f <- call fn $ (,[]) <$> papArgs ++ llArgs
        pure f
--    wht -> error $ show wht
--  wht -> error $ show wht
  StgPrim1 op -> mapM (stgToIR . StgLit) args >>= \case
    [a]   -> emitInstr (typeOf a) $ op a
  StgPrim2 op -> do
    mapM (stgToIR . StgLit) args >>= \case
      [a, b] -> emitInstr (typeOf a) $ op a b
  StgMkTuple -> stgMkTuple args
  StgGep     -> mapM (stgToIR . StgLit) args >>= \lArgs ->
                gep (head lArgs) (drop 1 lArgs)
                >>= (`load` 0)

-- StgApp
-- Arities always exactly match
-- Recall stack frames are responsible for data returned to them
-- We may need to alloca some stack space and pass that to the function
-- The fn might not yet be codegened, but should still be bound
stgToIR (StgApp iden args) = gets ((Map.!? iden) . bindMap)
  >>= \case
  Nothing -> stgConApp iden args -- Try the Data map
  Just x -> do -- Try the bindMap (regular/vanilla llvm fns)
--  traceM $ "args: " ++ show args
    let params = map (,[]) <$> llvmArgs
        llvmArgs = mapM (stgToIR . StgLit) args
    case x of
      ContPrim r _ _ _-> stgToIR (StgInstr r args)
      ContRhs (StgPrim p _ _) -> stgToIR (StgInstr p args)
      callable -> params >>= \p -> (`call` p) =<< case callable of
          ContLi f -> error "StgToIR ($): panic: unexpected literal"
          ContFn f -> pure f
          ContRhs (StgRhsSsa val) -> pure val -- a function pointer arg
          ContRhs rhs@StgTopRhs{} -> fnToLlvm iden rhs
          ContRhs rhs@(StgExt llvmTy) -> fnToLlvm iden rhs
          ContRhs r -> error ("cannot call non function: " ++ show r)

-- | case: produce a switch on a literal value
stgToIR (StgCase expr defaultBranch (StgSwitch alts)) = mdo
  let (vals, altCode) = unzip alts
  scrut <- stgToIR expr `named` "scrutinee"
  let genAlts expr = do -- collect (result,block) pairs to emit the phi instr
         b <- block
         r <- stgToIR expr
         br endBlock
         pure (r, b)
  switchAlts <- pure $ zip vals (map snd retBlockPairs)
  switch scrut dBlock switchAlts
  retBlockPairs <- mapM genAlts altCode
  dBlock <- block -- `named` "default_branch"
  dSsa <- case defaultBranch of
      Just code -> stgToIR code <* br endBlock
      Nothing   -> do
          errFn <- gets ((\(Just (ContFn f)) -> f) . (Map.!? "NoPatternMatchError") . bindMap)
          call errFn [] <* unreachable
  endBlock <- block -- `named` "endBlock"
  let phiBlocks = case defaultBranch of -- skip the 'void' default branch.
          Just _ -> (dSsa, dBlock) : retBlockPairs
          Nothing -> retBlockPairs
  phi phiBlocks

-- ********
-- * Data *
-- ********
-- Data case deconstruction. use deconProduct or deconSum from DataToLLVM.hs
-- maybeDefault is only used in sumtype deconstructions
stgToIR (StgCase scrut _ (StgDeconAlts []))
  = error "cannot deconstruct an empty sum type"
stgToIR (StgCase scrut maybeDefault (StgDeconAlts alts)) =
  stgToIR scrut >>= \dataStruct ->
  case alts of
     [p@(iden, membs, e)] -> deconProduct dataStruct p
                             >>= stgToIR . (`StgLet` e)
     alts -> stgToIR =<< deconSum dataStruct maybeDefault alts

stgMkTuple args = do
  llvmArgs <- mapM (stgToIR . StgLit) args
  let tys = typeOf <$> llvmArgs
  getOrMakeTuple tys >>= \case
    DataFns sz f [] Nothing ->
      let structTy = StructureType False tys
      in do
      dataTuple <- handleMemParam sz f args
      bitcast dataTuple (PointerType structTy (AddrSpace 0))
    _ -> error "internal problem with tuples: "

-- StgApp for constructors: we're responsible for memory returned to this stack frame
-- So if we don't return it here, it needs to be freed.
stgConApp :: CodeGenIRConstraints m
  => StgId -> [StgArg] -> m Operand
stgConApp iden baseArgs =
  gets ((Map.!? iden) . dataFnsMap) >>= \case
    Nothing -> error (show iden ++ ": unbound function")
    Just (ProxyDataFn sz fn)          -> handleMemParam sz fn baseArgs
    Just (DataFns sz con membs destr) -> handleMemParam sz con baseArgs

-- Data lifespan: Either 
-- * this stack frame returns it, -> write it to mem arg
-- * expires on this stack frame -> alloca (and maybe queue destructor)
-- * subdata -> malloc (a destructor will clean this later)
handleMemParam :: CodeGenIRConstraints m
  => StgConst -> StgFn -> [StgArg] -> m Operand
handleMemParam sz fn args = gets subData >>= \case
 True -> do
     mem <- gets ((\(Just (ContFn m))->m) . (Map.!? "malloc") . bindMap)       >>= \malloc -> call malloc [(ConstantOperand sz, [])]
     params <- map (,[]) <$> mapM (stgToIR . StgLit) args
     call fn ((mem,[]) : params)

 False -> gets stackFrame >>= \case
   -- No active stack frame -> this frame is responsible for this data
   Nothing -> do
       -- traceM "no active frame"
       modify (\x->x{ subData = True })
       mem <- alloca (IntegerType 8) (Just $ ConstantOperand sz) 0
       params <- map (,[]) <$> mapM (stgToIR . StgLit) args
       call fn ((mem,[]) : params)

   -- Use the current fns mem arg
   Just sf@(StackFrame stackSz memPtr destrQueue) -> do -- top data: give it stack mem
       -- traceM "active frame"
       -- eval params using the new stackframe state
       modify (\x->x{ subData = True })
       modify (\x->x{ stackFrame = Nothing })
       params <- map (,[]) <$> mapM (stgToIR . StgLit) args
       modify (\x->x{ stackFrame = Just sf })

       -- call the constructor with our stack memory
       let memArg = (memPtr, [Returned, NonNull])
       call fn (memArg : params)
