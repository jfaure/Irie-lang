module CodeGen (mkStg) where
import Prim
import Prim2LLVM
import Externs
import CoreSyn
import CoreUtils
import PrettyCore
import Control.Monad.ST.Lazy
import Control.Monad.State.Lazy
import Control.Monad.Primitive (PrimMonad,PrimState,primitive)
import Data.Functor
import Data.Function
import Data.Foldable
import Data.List (partition)
import Data.Char
import Data.Maybe
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Text as T
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.IntSet as IS
import qualified Data.ByteString.Short as BS
import qualified LLVM.AST as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.FloatingPointPredicate as FP
import qualified LLVM.AST.FunctionAttribute as FA
import qualified LLVM.AST.Type  as LT
import qualified LLVM.AST.Typed as LT
import qualified LLVM.AST.Float as LF
import           LLVM.AST.AddrSpace
import           LLVM.AST.Global
import           LLVM.AST.Linkage as L
import           LLVM.AST.CallingConvention as CC
import LLVM.IRBuilder.Module hiding (function)
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction hiding (gep)

import Debug.Trace
mkStg :: V.Vector Expr -> V.Vector (HName , Bind) -> L.Module
mkStg externBindings coreBinds = let
  mkVAFn ty nm = L.GlobalDefinition functionDefaults
    { name = L.mkName nm , linkage = L.External , parameters=([],True) , returnType = ty }
  nBinds = V.length coreBinds
  moduleDefs = runST $ do
    v <- V.thaw (TWIP <$> coreBinds)
    llvmDefs <$> execStateT (cgBind `mapM` [0 .. nBinds-1]) CGState {
        wipBinds = v
      , externs  = externBindings
      , llvmDefs =
--      (\x -> L.TypeDefinition (structName x) (Just $ rawStructType x)) `map` builtinStructs ++
        [
          mkVAFn voidPtrType "fralloc_mergeFrames"
        , mkVAFn voidPtrType "fralloc_shareFrames"
        , mkVAFn voidPtrType "fralloc_freeFrame"
        , mkVAFn intType "fralloc_isSingle"
        , mkVAFn voidPtrType "fralloc_newFrag"
        , mkVAFn voidPtrType "fralloc_freeFrag"

        , L.TypeDefinition "A" Nothing
        , L.TypeDefinition "ANY" Nothing
        , L.GlobalDefinition functionDefaults
          { name=L.mkName "printf"
          , linkage=L.External , parameters=([] , True) , returnType=intType }
        , L.GlobalDefinition functionDefaults
          { name=L.mkName "llvm.uadd.with.overflow.i32"
          , linkage=L.External , parameters=([] , True)
          , returnType=LT.StructureType False [intType , LT.IntegerType 1] }
        ]
      , moduleUsedNames = M.empty
      , stack = []
     }
  in L.defaultModule {
      L.moduleName = ""
    , L.moduleDefinitions = reverse $ moduleDefs
--  , L.moduleTargetTriple = Just "x86_64-unknown-linux-gnu" -- x86_64-pc-linux-gnu
--  , L.moduleDataLayout = Just "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
    }

--lookupArg i = gets ((IM.!? i) . regArgs . head . stack)
--  Nothing  -> gets envArgs >>= \e -> panic $ "arg not in scope: " ++ show i ++ "\nin: " ++ show (IM.keys <$> e)

-- Bindings vary from functions to types to constants to constexprs to instructions
cgBind :: IName -> CGEnv s StgWIP
cgBind i = gets wipBinds >>= \wip -> MV.read wip i >>= \case
 TWIP (nm , bind) -> let
   llvmNm = L.mkName (T.unpack nm)
   in mdo -- handle recursive refs using MonadFix
     MV.write wip i b
     b <- case bind of
       BindOK tt -> case tt of
         Core (Instr instr) ty -> STGFn [] <$>
           emitPrimFunction instr [intType , intType] intType
         Core t ty -> -- panic $ "not ready for constants:\n" ++ show tt
           dataFunction llvmNm [] [] t ty [] <&> \case
             STGFn [] op -> STGConstant op
             f -> f
           -- TODO ? llvm.global_ctors: appending global [ n x { i32, void ()*, i8* } ]
         CoreFn args free t ty -> dataFunction llvmNm args [] t ty []
         Ty ty -> LLVMTy <$> cgType ty
       ko -> error "panic Core failed to generate a valid binding"
     pure b
 x -> pure x

dataFunction :: L.Name -> [(IName, [TyHead])] -> [(IName , LT.Type)]
  -> Term -> [TyHead] -> [FA.FunctionAttribute]
  -> CGEnv s StgWIP
dataFunction llvmNm args free body ty attribs =
  let iArgs = fst<$>args ; iFree = fst<$>free
      isDataTy = any isDataTyHead
--    argMap = zip iArgs localArgs ++ zip iFree freeArgs
      (dArgs , rArgs) = partition (isDataTy . snd) args
  in do
  retTy <- cgType ty
--mainArgTys <- (\(i,t) -> (i,) <$> cgType t) `mapM` args
  rArgTys <- (cgType . snd) `mapM` rArgs
  dArgTys <- (cgType . snd) `mapM` dArgs

  (params , blocks) <- runIRBuilderT emptyIRBuilder $ do
    rParams <- (\ty -> L.LocalReference ty <$> fresh) `mapM` rArgTys
    dParams <- (\ty -> L.LocalReference ty <$> fresh) `mapM` dArgTys
    modify $ \x -> x {
     stack = CallGraph
     { regArgs  = IM.fromList$zip (fst<$>rArgs) rParams
     , dataArgs = IM.fromList$zip (fst<$>dArgs) ((\s->DataArg 0 s s)<$>dParams)
     , splits = []
     } : stack x }

    cgTerm body >>= (ret . op)
    s <- gets (head . stack)
    -- dup dataArgs
    modify $ \x -> x { stack = drop 1 (stack x) }
    pure (rParams ++ dParams)

  let fnParams = (\(L.LocalReference ty nm) -> Parameter ty nm []) <$> params
  STGFn iFree <$> emitFunction llvmNm fnParams retTy blocks

useArgs args = frAlloc_shareFrame `mapM` args

cgTerm' = fmap op . cgTerm
mkSTGOp x = STGOp x Nothing

cgTerm :: Term -> CGBodyEnv s STGOp
cgTerm = let
  cgName = \case
    VBind i -> lift (cgBind i) >>= \case
      STGConstant x -> mkSTGOp <$> x `call'` [] -- TODO where is the frame
      f -> pure $ mkSTGOp $ fnOp f
    -- Args: 1. regular args 2. dataArgs 3. splits from Match
    VArg  i -> gets (head . stack) >>= \cg -> case (regArgs cg IM.!? i) of
      Just reg -> pure $ mkSTGOp reg
      Nothing  -> case (dataArgs cg IM.!? i) of
        Just (DataArg shares frame op) -> let
--        mergeQTT plan cur 
          incUse = IM.update (\(DataArg q f o) -> Just $ DataArg (1 + q) f o) i
          -- someone (fn call or Split) used the darg
          in do
          modifySF (\x->x{ dataArgs = incUse (dataArgs cg) })
          pure $ STGOp op (Just frame)
        Nothing -> let
          doSplit s = (\op -> (sframe s , op)) <$> (components s IM.!? i)
          in case asum (doSplit <$> splits cg) of
          Just (f , o)  -> pure $ STGOp o (Just f)
          Nothing -> panic $ "arg not in scope: " ++ show i
    VExt  i -> _
  in \case
  Var vNm -> cgName vNm
  Lit l   -> mkSTGOp . L.ConstantOperand <$> lift (literal2Stg l)
  Instr i -> error $ show i -- cgPrimInstr i -- TODO top-level wrapper for instr
--MultiIf ((ifE,thenE):alts) elseE ->  -- convert to tree of switch-cases
--  genSwitch ifE [(C.Int 1 1 , thenE)] . Just $ case alts of
--    [] -> elseE
--    branches -> MultiIf branches elseE

  Cons fields      -> _ -- alloc =<< (cgTerm `mapM` fields)
  Proj  t f        -> _ -- cgTerm t >>= \t -> loadIdx t f
  Label i tts      -> do -- merge argframes
    rawTerms <- (cgTerm . (\(Core t ty) -> t)) `mapM` tts
    let args  = op <$> rawTerms
        labTy = LT.StructureType False $ sumTagType : (LT.typeOf <$> args)
        sz    = L.ConstantOperand $ C.sizeof labTy
        dFrames = catMaybes $ fr <$> rawTerms
    frame  <- frAlloc_mergeFrames (constI32 (fromIntegral $ length dFrames) : dFrames)
    outPtr <- frAlloc_new frame sz
    out    <- bitcast outPtr (LT.ptr labTy)
    zipWithM (storeIdx out) [0..length args] (constTag (fromIntegral i) : args)
    pure $ STGOp outPtr (Just frame)

  m@(Match ty labels d) -> -- mkSplitTree Nothing labels d
    panic $ "floating match" -- we need an argument to split on (this should have been lifted to a fn def)
  List  args       -> _

  App f args -> case f of
    Match ty alts d -> case args of
      [scrutCore] -> do
        stgScrut  <- cgTerm scrutCore
        retTy <- lift (cgType ty)
        let frame = fromMaybe (panic "no frame") $ fr stgScrut
            scrut = op stgScrut
        tag    <- load' =<< (`gep` [constI32 0]) =<< bitcast scrut (LT.ptr sumTagType)
        -- each branch is responsible for memory, frames etc..
        ourFrame <- frAlloc_isSingle frame -- TODO suspect
        let mkAlt l e = do
              (retOp , datas) <- genAlt ourFrame frame scrut l e
              (datas ,) <$> bitcast (op retOp) retTy
            branches = ("",) . uncurry mkAlt <$> (IM.toList alts)
        -- TODO find max data consumptions and make sure all branches consume this
        (datas , retOp) <- mkBranchTable tag branches
        pure $ STGOp retOp (Just ourFrame)
      bad -> panic $ "Match should have exactly 1 argument; not " ++ show (length bad)
    Instr i    -> mkSTGOp <$> cgInstrApp i args
    Var (VBind fI) -> lift (cgBind fI) >>= \case
      STGDataFn fnOp free datas -> do
        -- if f shares datas, we need to be at least as pessimistic with current datagroups
        let argShares = args
        -- call f with appropriate datagroups
        _
      STGFn free fptr -> mkSTGOp <$> (call' fptr =<< (cgTerm' `mapM` args))
    Var (VArg fI) -> _
    Var (VExt fI) -> _
    f -> panic "STG: floating function; expected binding index"
  --f -> cgTerm f >>= \f' -> call' f' =<< (cgTerm `mapM` args)

  x -> error $ "MkStg: not ready for term: " ++ show x

-- also return the args consumed (Match needs to uniformize this)
genAlt :: L.Operand -> L.Operand -> L.Operand -> ILabel -> Expr -> CGBodyEnv s (STGOp , IM.IntMap DataArg)
genAlt isOurFrame frame scrut lName (CoreFn args _free t ty) = do
  altType <- lift $ LT.ptr . LT.StructureType False . (sumTagType :) <$> (cgType `mapM` (snd <$> args))
  e   <- bitcast scrut altType
  llArgs <- loadIdx e `mapM` [1 .. length args]
  let newSplit = Split lName frame (IM.fromList $ zip (fst<$>args) llArgs)
   in modifySF $ \s->s{ splits = newSplit : splits s }
  frAlloc_freeFrag frame e (L.ConstantOperand $ C.sizeof $ LT.typeOf e) -- TODO too early ? sometimes pointless ?
  -- find out what dargs are consumed on this branch (which is conditionally executed !)
  oldDargs <- gets (dataArgs . head . stack)
  r <- cgTerm t
  diff <- let combineDArgs old@(DataArg s1 f1 d1) new@(DataArg s2 f2 d2) = DataArg (s2-s1) f2 d2
    in IM.unionWith combineDArgs oldDargs <$> gets (dataArgs . head . stack)
  modifySF $ \x -> x { splits = drop 1 (splits x) , dataArgs = oldDargs }
  pure $ (r , diff)

--retData  = isLabelTy . L.resultType . L.pointerReferent . LT.typeOf
--isDataFn = any isLabelTy . L.argumentTypes . L.pointerReferent . LT.typeOf
isDataFn = \case
  Var (VBind i) | i < 5 -> True
  x -> False
isLabelTy x = case x of
  LT.PointerType{} -> case LT.pointerReferent x of
    LT.NamedTypeReference nm -> nm==L.mkName "label"
    _ -> False
  _ -> False

isVoidTy x = case x of { LT.VoidType -> True ; x -> False }

cgInstrApp instr args = case instr of
    PutNbr -> call (L.ConstantOperand (C.GlobalReference (LT.ptr $ LT.FunctionType intType [] True) (L.mkName "printf"))) =<< (map (,[]) <$> cgTerm' `mapM` (Lit (String "%d\n") : args))
    CallExt nm -> let
      llvmNm = L.mkName (T.unpack nm)
      fn = C.GlobalReference (LT.ptr $ LT.FunctionType intType [] True) llvmNm
      in call (L.ConstantOperand fn) =<<  (map (,[]) <$> cgTerm' `mapM` args)
    Zext    -> (\[a] -> zext a intType) =<< (cgTerm' `mapM` args)
    IfThenE -> (\[ifE, thenE, elseE] -> genSwitch ifE [(C.Int 1 1 , thenE)] (Just elseE)) args
    AddOverflow -> _
    i -> emitInstr intType =<< (\instr [a,b] -> instr a b) (cgPrimInstr i) <$> (cgTerm' `mapM` args)

cgType :: [TyHead] -> CGEnv s L.Type
cgType = \case
  [t] -> cgTypeAtomic t
  [THExt 1 , _] -> pure $ intType
  x   -> pure polyType
--x   -> panic $ "lattice Type: " ++ show x

cgTypeAtomic = let
  voidPtrType = polyType -- tyLabel -- LT.ptr $ LT.StructureType False []
  in \case
  THExt i       -> gets externs >>= (cgType . tyExpr . (V.! i))
  THArrow tys t -> (\ars retTy -> L.FunctionType retTy ars False)
    <$> (cgType `mapM` tys) <*> cgType t
  x -> pure $ case x of
    THVar{}    -> voidPtrType
    THArg{}    -> voidPtrType
    THPrim p   -> primTy2llvm p
    THArray t  -> _ -- LT.ArrayType $ cgType t
    THSum   ls -> tyLabel
    THSplit ls -> tyLabel
    THProd p   -> voidPtrType
    THRec{}    -> tyLabel -- voidPtrType -- HACK
    x -> error $ "MkStg: not ready for ty: " ++ show x
tyLabel = voidPtrType -- HACK

cgPrimInstr i = case i of
  ExprHole -> _
  MkNum    -> _
  MkReal   -> _
  MkTuple  -> _
  Alloc    -> _
  Len      -> _
  SizeOf   -> _ -- C.sizeof
  x -> primInstr2llvm i

genSwitch :: Term -> [(C.Constant , Term)] -> Maybe Term -> CGBodyEnv s L.Operand
genSwitch scrutTerm branches defaultBranch = let
  callErrorFn str = _ -- call (errFn str) [] <* unreachable
  genAlt endBlock (scrutVal , expr) = do -- collect (result,block) pairs for the phi instr
    flip (,) <$> block <*> (cgTerm' expr <* br endBlock)
  in mdo
  scrut <- cgTerm' scrutTerm
  switch scrut dBlock (zip (fst <$> branches) (snd <$> retBlockPairs))
  dBlock   <- (block `named`"switchDefault")
  dSsa   <- case defaultBranch of
    Just d  -> cgTerm' d <* br endBlock
    Nothing -> callErrorFn "NoPatternMatch"
  retBlockPairs <- genAlt endBlock `mapM` branches
  endBlock <- block `named` "switchEnd"
  phi $ (dSsa, dBlock) : retBlockPairs

----------------
-- Primitives --
----------------
literal2Stg :: Literal -> CGEnv s C.Constant
literal2Stg l = let
  mkChar c = C.Int 8 $ toInteger $ ord c 
  in case l of
  Char c    -> pure $ mkChar c
  String s  -> flip emitArray (mkChar<$>(s++['\0'])) =<< freshTopName "str"
--Array  x  -> emitArray $ (literal2Stg <$> x)
  Int i     -> pure $ C.Int 32 i
--  Frac f    -> C.Float (LF.Double $ fromRational f)
  x -> error $ show x

-- generate fn for prim instructions (ie. if need a function pointer for them)
emitPrimFunction instr argTys retTy = do
  nm <- freshTopName "instr" -- TODO nah
  (params, blocks) <- runIRBuilderT emptyIRBuilder $ do
    params@[a,b] <- argTys `forM` \ty -> L.LocalReference ty <$> fresh
    ret =<< emitInstr (LT.typeOf a) ((primInstr2llvm instr) a b)
    pure params
  let fnParams = (\(L.LocalReference ty nm) -> Parameter ty nm []) <$> params
  emitFunction nm fnParams retTy blocks

emitFunction :: L.Name -> [Parameter] -> LT.Type -> [L.BasicBlock] -> CGEnv s L.Operand
emitFunction label fnParams retty blocks =
  let def = L.GlobalDefinition L.functionDefaults
        { name        = label
        , parameters  = (fnParams, False)
        , returnType  = retty
        , basicBlocks = blocks
        }
      argTys = (\(Parameter ty nm at)->ty) <$> fnParams
      funty = LT.ptr $ LT.FunctionType retty argTys False
      fnOp = L.ConstantOperand $ C.GlobalReference funty label
  in fnOp <$ emitDef def
