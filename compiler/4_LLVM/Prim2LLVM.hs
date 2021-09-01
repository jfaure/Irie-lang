{-# Language TypeFamilies #-}
module Prim2LLVM where
import Prim
import CoreSyn
import CoreUtils
import Externs
import Data.List (unzip3 , (!!))
import Data.String
import qualified Data.Text as T (pack)
import qualified Data.ByteString.Short as BS
import qualified Data.Vector.Mutable as MV
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.Vector as V
import qualified LLVM.AST as L
import qualified LLVM.AST.Type as LT
import qualified LLVM.AST.Typed as LT
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.FloatingPointPredicate as FP
import qualified LLVM.AST.Constant as C
import LLVM.AST.AddrSpace
import LLVM.AST.Global  as L
import LLVM.AST.Linkage as L
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction hiding (gep)

data SumKinds = Enum | Peano | Flat | SumTypeList | Tree

type CGEnv s a = StateT (CGState s) (ST s) a
type CGBodyEnv s a = IRBuilderT (StateT (CGState s) (ST s)) a
data CGState s = CGState {
 -- Input
   wipBinds   :: MV.MVector s StgWIP
 , externs    :: Externs --V.Vector Expr
 , coreModule :: JudgedModule

 -- Output
 , llvmDefs   :: [L.Definition]

 -- Internal State
 , stack           :: [CallGraph]
 , primDecls       :: Maybe (MV.MVector s (Maybe L.Definition))
 , gmpDecls        :: Maybe (MV.MVector s (Maybe L.Definition))
 , moduleUsedNames :: M.Map BS.ShortByteString Int
}

data DataArg = DataArg { qtt :: Int , aframe :: L.Operand , dOp :: L.Operand } deriving Show

data CallGraph = CallGraph {
   regArgs      :: IM.IntMap L.Operand
 , splits       :: [Split]   -- sumtypes split earlier on this SF
 , retLoc       :: Maybe L.Operand
 , dynRetDrops  :: Maybe L.Operand
 , retCast      :: Maybe BiCast
 , contextNm    :: [L.Name] -- for naming structs (eg. fn1.\.{})
} deriving Show

data RecordField = Dropped | Geppable | Gepped L.Operand deriving Show
data CGType
 = LLVMType   LT.Type
 | StructType (V.Vector L.Type) (Maybe L.Name)

-- Annotated llvm operands returned by terms. CGState Also passes down sret locations and a dyn retdrop array
-- Important ! codegen often matches partially on the CGOps it expects
-- This will obviously error if biunification slipped up, but better here than in llvm.
data CGOp
 = LLVMOp   { op' :: L.Operand } -- all info dynamically stored in here
 -- Note. Records. if we have a Just retloc in scope, we have to write out a struct
 -- Else we can track all its fields, only write it iff passed to function (byval)
 | RawFields{ fieldOps       :: V.Vector (CGOp , L.Type) }
 | Struct   { structOp       :: L.Operand
            , fieldTys       :: V.Vector L.Type
--          , structName     :: L.Name
            }
 | SubRecord{ structCGOp     :: CGOp
            , fieldTypes     :: V.Vector L.Type
            , localSubRecord :: V.Vector RecordField
--          , structName     :: L.Name
            }
 | LensAddr { structCGOp     :: CGOp -- what to return
            , lensTy         :: L.Type
            , lensAddr       :: CGOp -- L.Operand
            }
 | FunctionOp { fnPtrOp :: L.Operand
              , free    :: [IName]
              }
 | GMPFnOp    { fnPtrOp    :: L.Operand }
 | RecordFnOp { fnPtrOp    :: L.Operand
              , free       :: [IName]
              , fieldTypes :: V.Vector L.Type
              }
 deriving Show

markLoc :: BS.ShortByteString -> CGBodyEnv s L.Name
markLoc nm = mdo { br b ; b <- block `named` nm ; pure b }
op cgop = case cgop of
  LLVMOp o -> o
  x -> error $ show x

-- Commit all CGOp info to dynamic memory
cgOp2Arg :: CGOp -> CGBodyEnv s L.Operand
cgOp2Arg = \case
  LLVMOp o -> pure o

cgTypeOf = \case
  LLVMOp o -> LT.typeOf o

subCastRecord indxs = \case
  RawFields fs -> RawFields (V.fromList ((\i -> fs V.! i) <$> indxs))
  SubRecord struct fts subFs -> _
  Struct struct fieldTys -> Struct struct fieldTys
  Struct struct fieldTys -> SubRecord (LLVMOp struct) fieldTys mempty
  x -> error $ "not ready for: " <> show x

commitRecord :: Maybe L.Operand -> CGOp -> CGBodyEnv s CGOp
commitRecord retLoc r = let
  commitFields retLoc fieldTs newFields = do
    sret <- maybe (alloca' (mkStruct_tV fieldTs) Nothing) pure retLoc
    consStructV fieldTs sret newFields
    pure $ Struct sret fieldTs
  in case r of
  SubRecord (LLVMOp oldRecord) fTys subRecord -> let
    go newFieldOps i field = case field of
      Dropped  -> pure newFieldOps
      Gepped l -> pure (l : newFieldOps)
      Geppable -> (\l -> (l : newFieldOps)) <$> loadIdx oldRecord i
    in do
      newFields <- V.fromList <$> V.ifoldM go [] subRecord
      let fieldTs = LT.typeOf <$> newFields
      commitFields retLoc fieldTs newFields
--RawFields newFields -> commitFields retLoc (cgTypeOf <$> newFields) =<< (cgOp2Arg `mapM` newFields)
  RawFields newFields -> commitFields retLoc (snd <$> newFields) =<< ((cgOp2Arg . fst) `mapM` newFields)
  Struct struct fTys  -> let structTy = mkStruct_tV fTys in case retLoc of
    Just r -> Struct r fTys <$ (load' struct >>= store' r) -- need to copy an existing struct
  LensAddr struct lensTy vv@(LLVMOp v) ->   case retLoc of
    Just r -> LensAddr (LLVMOp r) lensTy vv <$ (load' v >>= store' r)
  x -> error $ "not ready for: " <> show x

mkSTGOp = LLVMOp

data Split = Split { -- a data opened by Match (may be reused or freed)
   lname      :: ILabel
 , sframe     :: L.Operand -- the parent frame
 , components :: IM.IntMap L.Operand -- datas here were split from this SF
} deriving Show
  
type DataFrame = L.Operand
modifySF f = modify $ \x->x { stack = (\(x:xs) -> f x : xs) (stack x) }
getSF :: CGBodyEnv s CallGraph
getSF = gets (fromJust . head . stack)
getRetLoc :: CGBodyEnv s (Maybe L.Operand)
getRetLoc = gets (retLoc . fromJust . head . stack)
setRetLocM :: Maybe L.Operand -> CGBodyEnv s ()
setRetLocM r = (modifySF $ \x->x {retLoc = r })
setRetLoc :: L.Operand -> CGBodyEnv s L.Operand
setRetLoc r = r <$ (modifySF $ \x->x {retLoc = Just r })
delRetLoc :: CGBodyEnv s ()
delRetLoc = modifySF $ \x->x {retLoc = Nothing }
getDelRetLoc :: CGBodyEnv s (Maybe L.Operand)
getDelRetLoc = getRetLoc <* delRetLoc

data FNRet
 = RetReg
 | RetRecord (V.Vector LT.Type)
 | RetBigint
 deriving Show

data StgWIP
 = TWIP   (HName , Bind)

 | STGFn       { retData :: !FNRet , freeArgs :: [IName] , fnOp :: L.Operand }
-- | STGDataFn { freeArgs :: [IName] , fnOp :: L.Operand , sts :: IM.IntMap QTT }
 | STGConstant { fnOp :: L.Operand } -- top level functions for now
 | STGConstantFn { fnOp :: L.Operand , freeArgs :: [IName] } -- top level functions for now

 | LLVMTy L.Type
 | LLVMInstr PrimInstr -- we avoid generating functions for these if possible
 deriving Show

getVAFn retTy nm = L.ConstantOperand (C.GlobalReference (LT.ptr $ LT.FunctionType retTy [] True) (L.mkName nm))

freshTopName :: BS.ShortByteString -> CGEnv s L.Name
freshTopName suggestion = do
  nameCount <- gets (fromMaybe 0 . (M.!? suggestion) . moduleUsedNames)
  modify $ \x->x{ moduleUsedNames = M.insert suggestion (nameCount + 1) (moduleUsedNames x) }
  pure $ L.Name $ "." <> suggestion <> "." <> fromString (show nameCount)

-- most llvm instructions take flags, stg wants functions on operands
primInstr2llvm :: PrimInstr -> (L.Operand -> L.Operand -> L.Instruction) = \case
 NumInstr n -> case n of
  BitInstr i  -> case i of
      And  -> \a b -> L.And             a b []
      Or   -> \a b -> L.Or              a b []
      Xor  -> \a b -> L.Xor             a b []
      ShL  -> \a b -> L.Shl False False a b []
      ShR  -> \a b -> L.LShr False      a b []
  IntInstr i  -> case i of
      Add  -> \a b -> L.Add False False a b []
      Sub  -> \a b -> L.Sub False False a b []
      Mul  -> \a b -> L.Mul False False a b []
      SDiv -> \a b -> L.SDiv False      a b []
      SRem -> \a b -> L.SRem            a b []
  PredInstr p -> case p of
      EQCmp-> \a b -> L.ICmp IP.EQ      a b []
      LECmp-> \a b -> L.ICmp IP.SLE     a b []
      GECmp-> \a b -> L.ICmp IP.SGE     a b []
      LTCmp-> \a b -> L.ICmp IP.SLT     a b []
      GTCmp-> \a b -> L.ICmp IP.SGT     a b []
  NatInstr i  -> case i of
      UDiv -> \a b -> L.UDiv False a b []
      URem -> \a b -> L.URem a b []
  FracInstr i -> case i of
      FAdd -> \a b -> L.FAdd L.noFastMathFlags a b []
      FSub -> \a b -> L.FSub L.noFastMathFlags a b []
      FMul -> \a b -> L.FMul L.noFastMathFlags a b []
      FDiv -> \a b -> L.FDiv L.noFastMathFlags a b []
      FRem -> \a b -> L.FRem L.noFastMathFlags a b []
      FCmp -> \a b -> L.FCmp FP.UEQ a b []
 t -> error $ show t

-- basically is it bigger than register size
isDataTyHead = \case { THTyCon (THProduct{})->True ; THPrim PrimBigInt->True ; THExt 21->True ; _->False } -- HACK
isStructTy  = \case { LT.StructureType{} -> True ; _ -> False }
isTypeRef   = \case { LT.NamedTypeReference{} -> True ; _ -> False }
isStructPtr = \case { LT.PointerType s _ -> isStructTy s ; _ -> False }
isTypeRefPtr = \case { LT.PointerType s _ -> isTypeRef s ; _ -> False }

primTy2llvm :: PrimType -> L.Type =
  let doExtern isVa tys =
        let (argTys, [retTy]) = splitAt (length tys -1) tys
        in LT.FunctionType retTy argTys isVa
  in \case
  PrimInt   i   -> LT.IntegerType $ fromIntegral i
  PrimBigInt    -> LT.NamedTypeReference "mpz_struct_t"
  PrimFloat f   -> LT.FloatingPointType $ case f of
      HalfTy    -> LT.HalfFP
      FloatTy   -> LT.FloatFP
      DoubleTy  -> LT.DoubleFP
      FP128     -> LT.FP128FP
      PPC_FP128 -> LT.PPC_FP128FP
  PtrTo ty      -> LT.PointerType (primTy2llvm ty) (AddrSpace 0)
  PrimExtern   argTys -> doExtern False (primTy2llvm <$> argTys)
  PrimExternVA argTys -> doExtern True  (primTy2llvm <$> argTys)
  PrimArr t     -> _
  PrimTuple tys -> -- StgTuple (primTy2llvm <$> tys)
    let structTy = LT.StructureType False (primTy2llvm <$> tys)
    in  LT.PointerType structTy (AddrSpace 0)

-- Module Builder
emitDef d = modify $ \x->x{llvmDefs = d : llvmDefs x}

emitArray :: L.Name -> [C.Constant] -> CGEnv s C.Constant
emitArray nm arr = let
 elemTy = LT.typeOf (fromJust $ head arr)
 llvmArr = C.Array elemTy arr
 ty = LT.typeOf llvmArr
 in C.GetElementPtr True (C.GlobalReference (LT.ptr ty) nm) [C.Int 32 0, C.Int 32 0]
   <$ (emitDef . L.GlobalDefinition) globalVariableDefaults
    { name        = nm
    , type'       = ty
    , linkage     = Private
    , isConstant  = True
    , initializer = Just llvmArr
    , unnamedAddr = Just GlobalAddr
    }

--------------------------
-- IRBuilder extensions --
--------------------------
-- horrible C typedefs
size_t     = i32_t  -- Note. any of unsigned char -> unsigned long long
int_t      = i32_t

mkStruct_tV= mkStruct_t . V.toList
mkStruct_t = LT.StructureType False
charPtr_t  = LT.ptr i8_t
iN_t       = LT.IntegerType
i1_t       = LT.IntegerType 1
i8_t       = LT.IntegerType 8
i32_t      = LT.IntegerType 32
i64_t      = LT.IntegerType 64
half_t : float_t : double_t : fP128_t : pPC_FP128_t = LT.FloatingPointType <$>
  [ LT.HalfFP , LT.FloatFP , LT.DoubleFP , LT.FP128FP , LT.PPC_FP128FP]

top_t = LT.ptr $ LT.NamedTypeReference "Top"
bot_t = LT.ptr $ LT.NamedTypeReference "Bot"
opaque_t    = LT.ptr $ LT.NamedTypeReference "Void"
voidPtrType = LT.ptr $ LT.NamedTypeReference "Void"
frameType   = LT.ptr $ LT.NamedTypeReference "Fr"
tagBits = 32
polyType = voidPtrType -- LT.ptr $ LT.NamedTypeReference "A"
charPtrType :: L.Type = LT.PointerType (LT.IntegerType 8) (AddrSpace 0)
intType     = LT.IntegerType 32
sumTagType  = LT.IntegerType tagBits
constTag    = L.ConstantOperand . C.Int tagBits
boolType    = LT.IntegerType 1
constIN b x = L.ConstantOperand (C.Int b x)
constI1     = constIN 1
constI32    = constIN 32
constI64    = constIN 64
polyFnType' = LT.FunctionType voidPtrType [] True -- `char* f(..)`
polyFnType  = LT.ptr polyFnType'
varArgsFnTy retTy = LT.ptr $ LT.FunctionType retTy [] True

load' ptr = load ptr 0
storePtr ty ptr op = bitcast ptr (LT.ptr ty) >>= \p -> store' p op
store' ptr op = store ptr 0 op
alloca' ty op = alloca ty op 0
call' f = call f . map (,[])
mkNullPtr = L.ConstantOperand . C.Null

gepTy ty addr is = emitInstr (LT.ptr ty) (L.GetElementPtr False addr is [])

-- TODO remove this
gep :: L.Operand -> [L.Operand] -> CGBodyEnv s L.Operand
gep addr is = let
  ty = gepType (LT.typeOf addr) is
  gepType ty [] = LT.ptr ty
  gepType (LT.PointerType ty _) (_:is') = gepType ty is'
  gepType (LT.StructureType _ elTys) ix = case ix of
    L.ConstantOperand (C.Int 32 val):is' -> if length elTys <= (fromIntegral val) then panic $ T.pack $ "gep: " ++ show val ++ show elTys else gepType (elTys !! fromIntegral val) is'
    x -> error "gep index: expected constI32"
  gepType (LT.VectorType _ elTy) (_:is') = gepType elTy is'
  gepType (LT.ArrayType _ elTy) (_:is') = gepType elTy is'
  gepType (LT.NamedTypeReference nm) is
--  | nm == structName label = gepType (rawStructType label) is
    | otherwise = panic $ T.pack $ "unknown typedef: " ++ show nm
  gepType x _ = error $ "gep into non-indexable type: " ++ show x
  in emitInstr ty $ (L.GetElementPtr False addr is [])

-- load a value from an array (~pointer to array)
zext' ty v = zext v ty
bitcast' a b = bitcast b a
--loadIdx :: L.Type -> L.Operand -> Int -> CGBodyEnv s L.Operand
--loadIdx fTy ptr i = load' =<< gep fTy ptr [constI32 0, constI32 $ fromIntegral i]
loadIdx :: L.Operand -> Int -> CGBodyEnv s L.Operand
loadIdx ptr i = load' =<< gep ptr [constI32 0, constI32 $ fromIntegral i]
storeIdx :: L.Type -> L.Operand -> Int -> L.Operand -> CGBodyEnv s ()
storeIdx fTy ptr i op = (`store'` op) =<< gepTy fTy ptr [constI32 0, constI32 $ fromIntegral i]

mkArray ar = let
  ty = LT.typeOf $ fromJust $ head ar
  undef = L.ConstantOperand $ C.Undef $ LT.ArrayType (fromIntegral$length ar) ty
  in foldM (\arr (i,val) -> insertValue arr val [i]) undef (zip [0..] ar)

-- make a list of pointers on the stack
mkPtrList :: LT.Type -> [L.Operand] -> CGBodyEnv s L.Operand
mkPtrList ty ops = do
  let len = length ops
      arrTy = LT.ArrayType (fromIntegral len) ty
      undef = L.ConstantOperand (C.Undef arrTy)
  ptr <- alloca' arrTy Nothing `named` "ptrList"
  arr <- foldM (\arr (i,val) -> insertValue arr val [i]) undef (zip [0..] ops)
  store' ptr arr
  pure ptr

--mkSizedPtrList ptrType ops = flip named "ptrListSZ" $  let -- + size variable
--  sz = fromIntegral $ length ops -- C.Int 32 (fromIntegral $ 1 + length ops)
--  arrTy = LT.ArrayType sz ptrType
--  structType = LT.StructureType False [ intType , arrTy ]
--  undef = L.ConstantOperand (C.Undef arrTy)
--  in do
--  ptr <- alloca' structType Nothing
--  storeIdx ptr 0 (constI32 $ fromIntegral sz)
--  ptrList <- foldM (\arr (i,v) -> insertValue arr v [i]) undef (zip [0..] ops)
--  storeIdx ptr 1 ptrList
--  pure ptr

consStructV fTys ptr vals = ptr <$ V.imapM (\i v -> storeIdx (fTys V.! i) ptr i v) vals
consStruct ptr vals = ptr <$ V.imapM_ (\i v -> storeIdx (LT.typeOf v) ptr i v) (V.fromList vals)

mkStruct :: Maybe L.Type -> [L.Operand] -> CGBodyEnv s L.Operand
mkStruct maybeTy vals = let
  ty    = case maybeTy of
    Nothing -> LT.StructureType False (LT.typeOf <$> vals)
    Just ty -> ty
  undef = L.ConstantOperand (C.Undef ty)
  in do
    ptr <- alloca' ty Nothing
    struct <- foldM (\struct (i,val) -> insertValue struct val [i]) undef (zip [0..] vals)
    ptr <$ store' ptr struct

pApAp pap papArity llArgs =
  (loadIdx pap `mapM` [0..1+papArity]) >>= \case
    fn : papArgs -> call fn $ (,[]) <$> papArgs ++ llArgs

-- TODO emit lookup tables for very likely case of juxtapposed tags
-- mkBranchTable :: Bool -> L.Operand -> [(BS.ShortByteString , CGBodyEnv s L.Operand)] -> CGBodyEnv s L.Operand
-- mkBranchTable doPhi scrut alts = mdo
--   switch scrut defaultBlock (zip (C.Int 32 <$> [0..]) entryBlocks)
--   (entryBlocks , phiNodes) <- unzip <$> alts `forM` \(blockNm , cg) -> do
--     b <- block `named` blockNm
--     code <- cg <* br endBlock
--     endBlock <- currentBlock
--     pure (b , (code , endBlock))
--   defaultBlock <- (block `named` "default") <* unreachable
--   endBlock <- block `named` "end"
--   if doPhi then phi phiNodes
--   else pure (L.ConstantOperand C.TokenNone)

mkBranchTable :: L.Operand -> [C.Constant] -> [(BS.ShortByteString , CGBodyEnv s CGOp)] -> CGBodyEnv s CGOp
mkBranchTable scrut labels alts = mdo
  switch scrut defaultBlock (zip labels entryBlocks)
  (entryBlocks , phiNodes , phiNodesFrames) <- unzip3 <$> alts `forM` \(blockNm , cg) -> do
    entry <- block `named` blockNm
    retOp <- op <$> cg
    br endBlock
--  STGOp retOp maybeDFrame struct <- cg <* br endBlock
    exit <- currentBlock
    pure (entry , (retOp , exit) , (,exit) <$> Nothing)
  defaultBlock <- (block `named` "default") <* unreachable
  endBlock <- block `named` "end"
  phiOp <- phi phiNodes
  dframe <- case catMaybes phiNodesFrames of
    []  -> pure Nothing
    ars -> Just <$> phi ars
  pure $ LLVMOp phiOp

cgType :: [TyHead] -> CGEnv s L.Type
cgType = \x -> case x of
  [t] -> cgTypeAtomic t
  [THExt 1 , _] -> pure $ intType
  [_ , THExt 1] -> pure $ intType
  x   -> pure polyType
--x   -> panic $ "lattice Type: " ++ show x

cgTypeAtomic = \case --x -> case did_ x of
  THExt i -> gets externs >>= (cgType . tyExpr . (`readPrimExtern` i))
  THTyCon t -> case t of
    THArrow   tys t -> (\ars retTy -> L.FunctionType retTy ars False) <$> (cgType `mapM` tys) <*> cgType t
    THProduct tyMap -> mkStruct_t <$> (cgType `mapM` IM.elems tyMap)
--  THSumTy   tyMap ->
--  THArray t  -> _ -- LT.ArrayType $ cgType t
--THVar v    -> gets (did_ . _pSub . (V.! v) . typeVars . coreModule) >>= cgType
--THArg a    -> gets (did_ . _mSub . (V.! a) . argTypes . coreModule) >>= cgType
--THRec r    -> gets (did_ . _pSub . (V.! r) . typeVars . coreModule) >>= cgType
  THVar{} -> panic "thvar found in codegen!" -- pure voidPtrType
  x -> pure $ case x of -- can be generated non monadically
    THTop    -> top_t
    THBot    -> bot_t
    THPrim p -> primTy2llvm p
    THSet  0 -> tyLabel
    x -> error $ "MkStg: not ready for ty: " ++ show x
tyLabel = voidPtrType -- HACK

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

--------------------
-- declare on use --
--------------------
mkExtDecl nm argTys retTy = L.GlobalDefinition functionDefaults
  { name=L.mkName nm
  , linkage = L.External , parameters=(map (\t -> Parameter t "" []) argTys , False)
  , returnType = retTy
  }

printf : snprintf : puts : strtol : atoi : abort : exit : system : rand : srand : llvm_stacksave : llvm_stackrestore : llvm_uadd_with_overflow_i32 : llvm_prefetch : llvm_abs : llvm_smax : llvm_smin : llvm_umax : llvm_umin : llvm_sqrt_f64 : llvm_powi_f64_i32 : llvm_pow_f64 : llvm_sin_f64 : llvm_cos_f64 : llvm_exp_f64 : llvm_exp2_f64 : llvm_log_f64 : llvm_log10_f64 : llvm_log2_f64 : llvm_floor_f64 : llvm_ceil_f64 : llvm_trunc_f64 : llvm_rint_f64 : llvm_memcpy_p0i8_p0i8_i64 : llvm_memmove_p0i8_p0i8_i64 : llvm_memset_p0i8_i64 : llvm_expect : llvm_load_relative_i32 : primDeclsLen : _ = [0..] :: [Int]

vecPrimDecls = V.fromList rawPrimDecls
rawPrimDecls =
 [ L.GlobalDefinition functionDefaults
    { name=L.mkName "printf" , linkage=L.External , parameters=([Parameter charPtr_t "" []],True) , returnType=i32_t }
 , L.GlobalDefinition functionDefaults
    { name=L.mkName "snprintf",linkage=L.External , parameters=([],True) , returnType=i32_t }
 , mkExtDecl "puts"   [charPtr_t] i32_t
 , mkExtDecl "strtol" [charPtr_t , LT.ptr charPtr_t , i32_t] i32_t
 , mkExtDecl "atoi"   [charPtr_t] i32_t
 , mkExtDecl "abort"  [] LT.VoidType
 , mkExtDecl "exit"   [i32_t] LT.VoidType
 , mkExtDecl "system" [charPtr_t] i32_t
 , mkExtDecl "rand"   [] i32_t
 , mkExtDecl "srand"  [i32_t] i32_t
 , mkExtDecl "llvm.stacksave"    [] charPtr_t
 , mkExtDecl "llvm.stackrestore" [charPtr_t] LT.VoidType
 , mkExtDecl "llvm.uadd.with.overflow.i32" [i32_t] (mkStruct_t [i32_t , i1_t])
 , mkExtDecl "llvm.prefetch" [charPtr_t , i32_t , i32_t ] LT.VoidType
 -- llvm stdlib (all are overloaded on bitwidth / floattype)
 , mkExtDecl "llvm.abs"  [i32_t] i32_t -- overloaded bitwidth
 , mkExtDecl "llvm.smax" [i32_t , i32_t] i32_t
 , mkExtDecl "llvm.smin" [i32_t , i32_t] i32_t
 , mkExtDecl "llvm.umax" [i32_t , i32_t] i32_t
 , mkExtDecl "llvm.umin" [i32_t , i32_t] i32_t
 , mkExtDecl "llvm.sqrt.f64" [double_t] double_t
 , mkExtDecl "llvm.powi.f64.i32" [double_t , i32_t] double_t
 , mkExtDecl "llvm.pow.f64"   [double_t , double_t] double_t
 , mkExtDecl "llvm.sin.f64"   [double_t] double_t
 , mkExtDecl "llvm.cos.f64"   [double_t] double_t
 , mkExtDecl "llvm.exp.f64"   [double_t] double_t
 , mkExtDecl "llvm.exp2.f64"  [double_t] double_t
 , mkExtDecl "llvm.log.f64"   [double_t] double_t
 , mkExtDecl "llvm.log10.f64" [double_t] double_t
 , mkExtDecl "llvm.log2.f64"  [double_t] double_t
 , mkExtDecl "llvm.floor.f64" [double_t] double_t
 , mkExtDecl "llvm.ceil.f64"  [double_t] double_t
 , mkExtDecl "llvm.trunc.f64" [double_t] double_t
 , mkExtDecl "llvm.rint.f64"  [double_t] i32_t
 -- fma etc..
 , mkExtDecl "llvm.memcpy.p0i8.p0i8.i64" [charPtr_t , charPtr_t , i64_t , i1_t] LT.VoidType
-- , mkExtDecl "llvm.memcpy.inline.p0i8.p0i8.i64" [charPtr_t , charPtr_t , i64_t , i1_t] LT.VoidType
 , mkExtDecl "llvm.memmove.p0i8.p0i8.i64" [charPtr_t , charPtr_t , i64_t , i1_t] LT.VoidType
 , mkExtDecl "llvm.memset.p0i8.i64" [charPtr_t , i64_t , i1_t] LT.VoidType

-- , mkExtDecl "llvm.ptrmask" [ptr_t , iN_t] ptr_t
 , mkExtDecl "llvm.expect.i1" [i1_t , i1_t] i1_t -- overloaded
 , mkExtDecl "llvm.load.relative.i32" [charPtr_t , i32_t] charPtr_t --load ptr + ptr[offset]
 ]

getPrimDecl :: Int -> CGEnv s L.Operand
getPrimDecl iname = let
  mkRef (L.GlobalDefinition f) = let
    argTys = (\(Parameter ty nm at)->ty) <$> fst (parameters f)
    fnTy = LT.FunctionType (L.returnType f) argTys (snd (parameters f))
    in L.ConstantOperand $ C.GlobalReference (LT.ptr fnTy) (L.name f)
 
  getDecl iname v = MV.read v iname >>= \case
    Just op -> pure $ mkRef op
    Nothing -> let val = vecPrimDecls V.! iname
      in mkRef val <$ MV.write v iname (Just val)

  in gets primDecls >>= \case
    Nothing -> MV.replicate primDeclsLen Nothing >>= \v -> do
      modify $ \x->x{ primDecls = Just v }
      getDecl iname v
    Just  v -> getDecl iname v
