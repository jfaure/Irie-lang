module CodeGen (mkStg) where
import Prim
import Prim2LLVM hiding (gep)
--import Externs
import CoreSyn
import CoreUtils
import Eval
import PrettyCore ({-number2xyz ,-} number2CapLetter)
import qualified GMPBindings as GMP
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Mutable as MV
import qualified Data.Text as T
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.String as DS
import qualified LLVM.AST as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.FunctionAttribute as FA
import qualified LLVM.AST.Type  as LT
import qualified LLVM.AST.Typed as LT
--import qualified LLVM.AST.ParameterAttribute as LP
import qualified LLVM.AST.IntegerPredicate as IP
import           LLVM.AST.Global
import           LLVM.AST.Linkage as L
--import qualified LLVM.AST.IntegerPredicate as IP
--import           LLVM.AST.CallingConvention as CC
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction as LIR hiding (gep)

--mkStg :: V.Vector Expr -> V.Vector (HName , Bind) -> V.Vector QTT -> L.Module
mkStg externBindings coreMod@(JudgedModule modName bindNames pFields pLabels coreBinds) = let
  mkVAFn ty nm = L.GlobalDefinition functionDefaults
    { name = L.mkName nm , linkage = L.External , parameters=([],True) , returnType = ty }
  nBinds = V.length coreBinds
  nFields = M.size pFields
  nLabels = M.size pLabels

  moduleDefs = runST $ do
    v  <- V.unsafeThaw (TWIP <$> V.zip bindNames coreBinds)
    st <- execStateT (cgBind `mapM` [nBinds-1 , nBinds-2 .. 0]) CGState {
        wipBinds = v
      , normFields = argSort nFields pFields
      , normLabels = argSort nLabels pLabels
--    , externResolver = extResolver
      , gmpDecls  = Nothing
      , primDecls = Nothing
      , externs  = externBindings
      , coreModule = coreMod
      , typeVars   = 0
      , llvmDefs = [
          L.TypeDefinition "Void"Nothing
--      , L.TypeDefinition "Bot"Nothing
        , L.TypeDefinition "Top"Nothing
        ]
      , moduleUsedNames = M.empty
      , stack = []
     }
    gmpDecls <- case gmpDecls st of
      Nothing -> pure []
      Just i  -> let
        gmpDefs =
          [ L.TypeDefinition "mpz_struct_t" (Just GMP.mpz_struct_t)
          , L.TypeDefinition "mpq_struct_t" (Just GMP.mpq_struct_t)
          ]
        in (gmpDefs ++)  . catMaybes . V.toList <$> V.unsafeFreeze i
    primDecls <- case primDecls st of
      Nothing -> pure []
      Just i  -> catMaybes . V.toList <$> V.unsafeFreeze i
    let tVs = (\i -> L.TypeDefinition (DS.fromString $ T.unpack $ number2CapLetter i) Nothing) <$> [0 .. typeVars st - 1]
    pure $ tVs ++ primDecls ++ gmpDecls ++ llvmDefs st
  in L.defaultModule {
      L.moduleName        = DS.fromString $ T.unpack modName
    , L.moduleDefinitions = moduleDefs
--  , L.moduleTargetTriple = Just "x86_64-unknown-linux-gnu" -- x86_64-pc-linux-gnu
--  , L.moduleDataLayout = Just "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
    }

-- Bindings vary from functions to types to constants to constexprs to instructions
-- maybe use llvm.global_ctors: appending global [n x { i32, void ()*, i8* }]
cgBind :: IName -> CGEnv s StgWIP
cgBind i = gets wipBinds >>= \wip -> MV.read wip i >>= \case
 TWIP (nm , bind) -> let
   strNm  = T.unpack nm
   llvmNm = L.mkName strNm -- bit sad llvm..
   cgExpr = \case
     Core (Abs args free t _ty) ty -> let
       (argTys , retTy) = getArrowArgs ty
       as = zipWith (\(i,_) t -> (i,t)) args argTys
       in dataFunction i llvmNm as [] t retTy [] -- TODO fragile (paps ? etc..)
     -- partialApp is an abs with implicit arguments
     Core t@(PartialApp argTs fn args) ty -> let
       (papArTs , papRetT) = getArrowArgs ty
--     as      = zipWith (\(i,_) t -> (i,t)) args argTys
       papArgs = zip (negate <$> [1..] :: [Int]) argTs -- papArTs
       termPapArgs = (\(i,_) -> Var (VArg i)) <$> papArgs
       patchTerm = App fn (args ++ termPapArgs)
       in dataFunction i llvmNm papArgs [] patchTerm papRetT []
     Core t ty -> dataFunction i llvmNm [] [] t ty [] -- <&> \case { STGFn _ [] op -> STGConstant op ; f -> f }
     PoisonExpr -> panic $ "attempted to codegen a poison expr: " <> nm
     Ty ty -> LLVMTy <$> cgType ty
   in do
--   MV.write wip i b --(STGConstant $ getVAFn LT.VoidType strNm) -- don't handle recursive refs using MonadFix
     b <- case bind of
       BindOK tt    -> cgExpr tt
       BindOpt _ tt -> cgExpr tt
       ko -> panic $ "panic Core failed to generate a valid binding: " <> nm
     b <$ MV.write wip i b --(STGConstant $ getVAFn LT.VoidType strNm)
 x -> pure x

-- DataFunctions pass extra frame arguments with their data args
-- The full CGOp signature must be computed independent of the body in order to handle recursive references !
dataFunction :: IName -> L.Name -> [(IName, [TyHead])] -> [(IName , LT.Type)]
  -> Term -> [TyHead] -> [FA.FunctionAttribute]
  -> CGEnv s StgWIP
dataFunction bindINm llvmNm args free body returnType attribs = cgType returnType >>= \retTy -> let
    iArgs = fst<$>args ; iFree = fst<$>free
    dataRetKind = \case
      THPrim (PrimBigInt)   -> RetBigint
      THTyCon (THProduct{}) -> RetRecord (V.fromList $ getStructFieldTys retTy)
      THBound{}             -> _
      _                     -> RetReg
    retKind  = dataRetKind ((\[x] -> x) returnType)
    hasSRet  = case retKind of { RetBigint -> True ; RetRecord{} -> True ; _ -> False }
    isDataTy = any isDataTyHead
    retData  = isDataTy returnType
    rArgs = args
    mkTyconPtr t = case t of -- tycon Function arguments are always pointers (can annotate structs with byval)
      LT.StructureType{}      -> LT.ptr t
      LT.NamedTypeReference{} -> LT.ptr t
      LT.FunctionType      {} -> LT.ptr t
      t -> t
    retDropFieldsTy = LT.ArrayType (fromIntegral $ length (getStructFieldTys retTy)) i1_t
  in do
  rawArgTys <- (cgType . snd) `mapM` rArgs
  let rArgTys  = mkTyconPtr <$> rawArgTys -- structs , functions and label arguments are always pointers
      llvmArgTys   = case retData of
        False -> rArgTys
        True  -> if isTypeRef retTy then LT.ptr retTy : rArgTys else LT.ptr retTy : retDropFieldsTy : rArgTys
      fnParams = zipWith (\nm ty -> Parameter ty (L.UnName nm) []) ([0..] :: [Word]) llvmArgTys

  -- write the fn declaration already
      llvmRetT = if retData then LT.VoidType else retTy
      funty = LT.ptr $ LT.FunctionType llvmRetT llvmArgTys False
      fnPtr = L.ConstantOperand $ C.GlobalReference funty llvmNm
      stgFn = if null fnParams then STGConstantFn fnPtr iFree else STGFn retKind llvmArgTys llvmRetT iFree fnPtr Nothing
  gets wipBinds >>= \wip -> MV.write wip bindINm stgFn

  (_ {-(complex' , (retTy' , fnParams'))-} , blocks) <- runIRBuilderT emptyIRBuilder $ do
    (retPtr , rd) <- case retData of
      False -> pure (Nothing , Nothing)
      True  -> do
        rp <- Just . L.LocalReference (LT.ptr retTy) <$> fresh
        rd <- if isTypeRef retTy then pure Nothing else Just . L.LocalReference retDropFieldsTy <$> fresh
        pure (rp , rd)
    rParams <- rArgTys `forM` \ty -> L.LocalReference ty <$> fresh
    let cgArgOps = (flip map) rParams $ \llop@(L.LocalReference ty nm) -> case ty of
          LT.PointerType x _ -> case x of
            LT.StructureType _ elems -> Struct llop (V.fromList elems)
            LT.NamedTypeReference _  -> LLVMOp llop -- TODO GMPOp ?
          primType -> LLVMOp llop

    modify $ \x -> x { stack = CallGraph
     { regArgs     = IM.fromList $ zip (fst<$>rArgs) cgArgOps -- rParams
     , splits      = []
     , retLoc      = retPtr
     , retCast     = Nothing
     , dynRetDrops = rd
     , complexity  = 0
     , contextNm   = [llvmNm]
     } : stack x }
--  (papParams , finalRetTy) <- cgTerm body >>= \case
--    PapOp (FunctionOp fnPtr~ free argT retT) captures -> do
--      papArgs <- drop (length captures) argT `forM` \ty -> L.LocalReference ty <$> fresh `named` "papArgs"
--      -- TODO cgOpApp , don't commit Arg here !
--      commitArg `mapM` captures >>= \capturedDyn -> call' fnPtr (capturedDyn ++ papArgs) >>= ret
--      pure (papArgs , retT)
--    ~sret -> ([] , retTy) <$ if retData then retVoid else ret (op sret)
    cgTerm body >>= \result -> if retData then retVoid else ret (op result)
    modify $ \x -> x { stack = drop 1 (stack x) }

    let mkParam attrib = (\(L.LocalReference ty nm) -> Parameter ty nm attrib)
    pure ()
--      fnParams = mkParam [] <$> (rParams ++ papParams) -- ! recursion means we cannot depend on codegen
--      fnParams = mkParam [] <$> rParams -- ! recursion means we cannot depend on codegen
    -- llvm: "functions with sret must return void", for abi compatibility:
    -- The x86-64 ABIs require byval struct returns be copied into %rax|%eax
--  pure $ (_,) <$> if hasSRet then (LT.VoidType , fnParams) else (retTy , fnParams)
--  pure $ (complex , ) $ case (retPtr , rd) of
--    (Just sret , Just rd) -> (LT.VoidType , mkParam [LP.SRet] sret : mkParam [] rd : fnParams)
--    (Just sret , Nothing) -> (LT.VoidType , mkParam [LP.SRet] sret : fnParams)
--    _         -> (finalRetTy , fnParams)

--let (retTy , fnParams) = if hasSRet then (LT.VoidType , rArgTys)
--  Warning! this cannot depend on information obtained through codegen else it breaks the mdo handling recursion
  emitFunction llvmNm identity fnParams llvmRetT blocks <&> \(~fptr) -> if null fnParams
    then STGConstantFn fptr iFree
--  else STGFn retKind llvmArgTys retTy iFree fptr Nothing --(if complex < 2 then Just (fst <$> args , body) else Nothing)
    else STGFn retKind llvmArgTys llvmRetT iFree fptr Nothing --(if complex < 2 then Just (fst <$> args , body) else Nothing)

getGMPRetPtr :: Bool -> CGBodyEnv s L.Operand
getGMPRetPtr doInit = (getRetLoc <* delRetLoc) >>= \retLoc -> let
  initGMP = alloca' GMP.mpz_struct_tname Nothing >>= if doInit then GMP.initSRetGMP else pure
  in maybe initGMP pure retLoc --(bitcast' GMP.mpz_t)

cgTerm' t = cgTerm t <&> \case -- cancer function
  LLVMOp o -> o
  f -> error $ "cgTerm': " <> show f

getStructFieldTys = \case             -- cancer function
  LT.StructureType _ elems -> elems
  LT.PointerType s _       -> getStructFieldTys s
  x -> error $ "expected struct type, got: " <> show x

getCastRetTy ty = \case
  CastInstr GMPZext{} -> GMP.mpz_struct_tname
  BiEQ -> (\(LT.PointerType t _ ) -> t) ty
  x -> error $ "not done yet: " <> show x

-- cgArg = commit2mem <=< cgTerm
-- We cannot pass cgOP information through llvm function calls , so write any important info to dynamic memory
cgArg  :: Term -> CGBodyEnv s L.Operand
cgArg t = cgTerm t >>= commitArg

commitArg :: CGOp -> CGBodyEnv s L.Operand
commitArg = \case
  LLVMOp o -> pure o
  x -> error $ "not ready to mk arg with: " <> show x

-- conv CGOps to llvmOps and call appropriately
-- TODO use cgop info when possible
cgOpaqueApp :: L.Operand -> [Term] -> CGBodyEnv s L.Operand
cgOpaqueApp fOp argOps = call' fOp =<< (cgArg `mapM` argOps)

cgTerm :: Term -> CGBodyEnv s CGOp
cgTerm = let
  cgName = \case
    VBind i -> lift (cgBind i) >>= \case
      STGConstant f -> pure (LLVMOp f)
      STGConstantFn f free  -> LLVMOp <$> f `call'` []
      STGFn retData argT retT free ~fptr inlineable -> let
        cgOp = case retData of
          RetReg        -> FunctionOp fptr free argT retT
          RetRecord fts -> RecordFnOp fptr free fts
          RetBigint     -> GMPFnOp fptr
        in pure $ maybe cgOp (Inlineable cgOp) inlineable
    -- Args: 1. regular args 2. dataArgs 3. splits from Match
    VArg  i -> getSF >>= \cg -> case (regArgs cg IM.!? i) of
      Just reg -> pure reg
      Nothing  -> let
        doSplit s = (\op -> (sframe s , op)) <$> (components s IM.!? i)
        in case asum (doSplit <$> splits cg) of
        Just (f , o)  -> pure $ o --STGOp o (Just f) Nothing
        Nothing -> panic $ T.pack $ "arg not in scope: " ++ show i
    VExt  i -> _
  -- record field access (avoid loading inline structs)
  in \x -> case x of
  Var vNm     -> cgName vNm
  Lit (Int i) -> pure $ LLVMOp (constI32 i)
  Lit l   -> mkSTGOp . L.ConstantOperand <$> lift (literal2Stg l)
  Instr i -> lift (emitInstrWrapper i)
--Abs args free t ty -> lift $ freshTopName "lam" >>= \nm ->
--  dataFunction nm args [] t ty []
--MultiIf -> mkMultiIf ifsE elseE
  Label i tts      -> _
  List  args       -> _
  m@(Match ty labels d) -> panic $ "floating match" -- cgTerm (Abs .. ) fresh arginames somehow

  Cons fields      -> (getRetLoc <* delRetLoc) >>= \rl -> mkRecord rl fields

  -- Note. the record in question will be already casted (ie. address resolved | raw fields if lensOver changes a field's size)
  -- TODO rm all except LensAddr cgops
  TTLens tt _fields lens -> getRetLoc >>= \retLoc -> case lens of
    -- LensOver implemented as a Cast
    LensSet t -> error $ show lens
    LensGet -> let
      gepAddr = [constI32 0 , constI32 0] -- constI32 (fromIntegral field)
      in cgTerm tt >>= \case
      -- local struct
      LensAddr record lensTy cgLoc -> case cgLoc of
        RawFields fs -> pure cgLoc
        LLVMOp    i  -> pure cgLoc -- gepTy lensTy i gepAddr >>= loadField lensTy
--      in case record of
--      RawFields fs       -> pure $ fst $ fs V.! 0
--      Struct struct fTys -> gepTy lensTy struct gepAddr >>= loadField lensTy
--
      -- struct pointer passed in as an argument to this function:
      -- this maybe should have been promoted from singleton record to field
      Struct struct fVals -> let
        lensTy = fVals V.! 0 -- field
        in gepTy lensTy struct gepAddr >>= loadField lensTy
--    RawFields fs -> pure (fst $ fs V.! 0)
      x -> error $ "lens expected LensAddr or Struct: " <> show x

  Cast cast term -> doCast cast term

  App f args -> cgApp f args -- <* modifySF (\x->x{complexity=complexity x + 1})

  x -> error $ "MkStg: not ready for term: " <> show x

-- loadField: only load if primitive
loadField lensTy loc = if isStructTy lensTy --  || isTypeRef lensTy
  then pure $ Struct loc (V.fromList $ getStructFieldTys lensTy)
  else if isTypeRef lensTy -- GMP thing basically
  then pure $ LLVMOp loc
  else LLVMOp <$> load' loc

productCast2dropMarkers :: Int -> [(ASMIdx , BiCast)] -> (Int , [Int])
productCast2dropMarkers drops leafCasts = let -- mark dropped fields
  go (asmIdx , _) (len , acc) = (\next -> (1+len , next : acc)) $ if asmIdx == len then 0 else 1
  in foldr go (0 , []) leafCasts

-- catch some special term Apps here
cgApp f args = case f of
  Match ty alts d -> _ --emitMatchApp args ty alts d
  Instr i   -> case i of -- ifThenE is special since it can return data
    IfThenE -> case args of { [ifE, thenE, elseE] -> mkIf ifE thenE elseE }
    _ -> cgInstrApp Nothing i args
  Var{} -> cgTerm f >>= \case
--  LLVMOp fnOp -> cgOpaqueApp fnOp args <&> LLVMOp
    Inlineable cgOp (argNms , termFn) -> cgTerm (etaReduce argNms args termFn) -- TODO align args into PAp
    FunctionOp fptr free aTs rT -> cgOpaqueApp fptr args <&> LLVMOp
    GMPFnOp fptr -> cgTerm `mapM` args >>= \ars -> getGMPRetPtr True >>= \rl -> LLVMOp rl <$ callCGOp (LLVMOp fptr) (LLVMOp rl : ars)
    x -> error $ "cgapp :" <> show x
  other -> error $ "cgapp: " <> show other

-- recordApp can pass information to the record function
recordApp recordFn retLoc prodCast args = let
  evalCast r = case prodCast of
    CastProduct drops leaves -> doProductCast retLoc leaves r
    CastOver asmIdx preCast (Core fn _) retTy -> case r of
      Struct struct fTys -> let fTy = fTys V.! asmIdx
        in cgTerm fn >>= \f ->
           if isStructTy fTy || isTypeRef fTy
           then _ -- TODO pass down sret
           else do
             retT <- lift $ cgType retTy
             loadIdx struct asmIdx >>= call' (fnPtrOp f) . (:[]) >>= storeIdx retT struct asmIdx
             pure $ Struct struct (modifyField fTys asmIdx retT)

  in case recordFn of
  RecordFnOp fptr free fTys -> do
    args <- cgTerm' `mapM` args
    r <- callRecordFn retLoc fTys fptr args -- (productCast2dropMarkers drops leaves) sretTy fTys fptr args
    evalCast r

  Inlineable cgOp (argNms , termFn) -> cgTerm (etaReduce argNms args termFn) >>= -- TODO align args into PAp
    \r -> evalCast r
  fn -> error $ "recordApp expected RecordFnOp or Inlineable: " <> show fn

-- TODO inspect arguments
callCGOp cgFn cgArgs = let
  getOp = \case
    LLVMOp op -> op
    x -> error $ show x
  in case cgFn of
  FunctionOp fptr free at rt -> LLVMOp <$> call' fptr (getOp <$> cgArgs)
  PapOp fn captures          -> callCGOp fn (captures ++ cgArgs)
  -- gmp functions
  LLVMOp fptr                -> LLVMOp <$> call' fptr (getOp <$> cgArgs)
  x -> error $ show x

doCast :: BiCast -> Term -> CGBodyEnv s CGOp
doCast cast term = (getRetLoc <* delRetLoc) >>= \rl -> let
  prodCast leaves term = case term of
    App f args      -> cgTerm f >>= \fn -> recordApp fn rl cast args
    f@(Var VBind{}) -> cgTerm f >>= \fn -> recordApp fn rl cast [] -- ie. dodge args / intermediates
    _               -> cgTerm term >>= doProductCast rl leaves
  in case cast of
  BiEQ                     -> setRetLocM rl *> cgTerm term
  CastInstr i              -> cgInstrApp rl i [term]
  CastApp ac pap rc        -> error $ "cast app: " <> show cast
  CastProduct drops leaves -> prodCast leaves term
  CastOver asmIdx preCast (Core fn _) retTy -> cgTerm term >>= \case
    fnRet@RecordFnOp{} -> recordApp fnRet rl cast []
    Inlineable cgOp (argNms , termFn) -> _ --cgTerm (etaReduce argNms [] termFn) -- TODO align args into PAp
    RawFields fs -> do
      cgFn <- cgTerm fn
      val  <- callCGOp cgFn [fst (fs V.! asmIdx)]
      retT <- lift (cgType retTy)
      pure $ RawFields (modifyField fs asmIdx (val , retT))
    x -> error $ "expected recordfnOp: " <> show x
  x -> error $ "cast: " <> show x

doCastOp :: BiCast -> CGOp -> CGBodyEnv s CGOp
doCastOp cast operand = case cast of
  BiEQ        -> pure operand
  CastInstr i -> LLVMOp <$> cgOpInstr i [op operand]
  CastProduct d leaves -> (getRetLoc <* delRetLoc) >>= \rl ->
    doProductCast rl leaves operand

-- casting products with a retloc requires writing to memory
doProductCast :: Maybe L.Operand -> [(ASMIdx , BiCast)] -> CGOp -> CGBodyEnv s CGOp
doProductCast retLoc leaves r = let
  -- cast all fields, write to maybeSret
  fullCast eitherStructFields fTys leavesL = let
      leaves       = V.fromList leavesL
      castedFTys   = V.zipWith getCastRetTy fTys (snd <$> leaves)
      castedStruct = mkStruct_tV castedFTys
      readField sret getField retIdx (retTy , (leafIdx , leafCast)) = let
        leafTy     = fTys V.! retIdx
        retStruct  = isStructTy retTy  || isTypeRef retTy
        leafStruct = isStructTy leafTy || isTypeRef leafTy
        writeRetLoc retLoc leafPtr casted = case retLoc of
          Just retLoc -> do
            unless retStruct (store' retLoc casted) -- save non-struct leaf casts (they ignore our retLoc)
            -- if leafcast wasn't casted, it wasn't written to sret, so do it now:
            when (case leafCast of { BiEQ -> True ; _ -> False }) (load' leafPtr >>= store' retLoc)
          Nothing     -> pure ()
        in do
        retLoc <- case sret of
          Nothing   -> pure Nothing
          Just sret -> do
            retLoc <- gepTy retTy sret [constI32 0 , constI32 $ fromIntegral retIdx] `named` "retloc"
            Just retLoc <$ when retStruct (void (setRetLoc retLoc))

        case eitherStructFields of
          Left rawFs   -> let (val , ty) = rawFs V.! leafIdx in do
            casted <- doCastOp leafCast val
            -- non casted fields must be copied
            when (case leafCast of { BiEQ -> True ; _ -> False }) $ maybe (pure ()) (\retLoc -> load' (op val) >>= store' retLoc) retLoc
            pure $ casted
          Right struct -> do
            leafPtr <- gepTy leafTy struct [constI32 0 , constI32 $ fromIntegral leafIdx] `named` "leafptr"
            leaf    <- loadField leafTy leafPtr -- if leafStruct then pure leafPtr else load' leafPtr `named` "loadleaf"
            casted  <- doCastOp leafCast leaf `named` "casted"
            writeRetLoc retLoc leafPtr (op casted)
            pure $ casted
    in do
    markLoc "productCast"
    rawFields <- V.imapM (readField retLoc eitherStructFields) (V.zip castedFTys leaves)
    pure $ case retLoc of
      Nothing  -> RawFields $ V.zip rawFields castedFTys
      Just sret-> Struct sret castedFTys

  getRawFields struct fTys = case leaves of
    -- frequent case of Lens targeting a single field
    [(asmIdx , cast)] -> case struct of
      Right struct -> let fTy = fTys V.! asmIdx in do
        val <- doCastOp cast =<< loadField fTy =<< gepTy fTy struct [constI32 0 , constI32 $ fromIntegral asmIdx]
        pure $ LensAddr (Struct struct fTys) (fTys V.! asmIdx) val
      Left  rawFs  -> let field = rawFs V.! asmIdx in do
        val <- doCastOp cast (fst field)
        traceShowM val
        pure $ LensAddr (RawFields (modifyField rawFs asmIdx (val , cgTypeOf val))) (snd field) val
    leavesL      -> fullCast struct fTys leavesL

  in do
  casted <- case r of
    Struct struct fTys -> getRawFields (Right struct) fTys
    RawFields fieldOps -> let (fOps , fTys) = V.unzip fieldOps
      in getRawFields (Left fieldOps) fTys -- raw fields needn't be read from a struct ptr
    x -> error $ "cannot product-cast non-struct !: " <> show leaves <> "\n" <> show x
  case retLoc of
    Just r  -> commitRecord (Just r) casted -- (subCastRecord (fst <$> leaves) r)
    Nothing -> pure casted -- no need to write to memory atm

--callRecordFn (fieldCount , dropMarkers) superType ty fn args = let
callRecordFn retLoc fTys fptr args = let
  fieldCount = V.length fTys
  ty = mkStruct_tV fTys
  maskTy = LT.ArrayType (fromIntegral fieldCount) i1_t
--arr    = L.ConstantOperand (C.Array i1_t (C.Int 1 . fromIntegral <$> dropMarkers))
  arr    = L.ConstantOperand (C.Array i1_t (replicate fieldCount (C.Int 1 0)))
  newLocalSret = alloca' ty Nothing `named` "localSRet" >>= GMP.initGMPFields fTys
  mkRecordSRet = maybe newLocalSret pure retLoc
  in mkRecordSRet >>= \sret -> call' fptr (sret : arr : args) $> Struct sret fTys

-- mk Record ; if retloc given, write to mem, else take the raw fields
mkRecord :: Maybe L.Operand -> IM.IntMap Term -> CGBodyEnv s CGOp
mkRecord retLoc coreFieldsMap = gets normFields >>= \nf -> let
  fieldsMap = IM.mapKeys (nf VU.!) coreFieldsMap
  fLen = IM.size fieldsMap -- TODO this is O(n) !
  in case retLoc of
    Nothing   -> (cgTerm `mapM` IM.elems fieldsMap) <&> \fs -> let fields = V.fromList fs
      in RawFields $ V.zip fields (cgTypeOf <$> fields)
    Just sret -> do -- spawn a struct , don't write to subcasted fields
      dynRetDrops <$> getSF >>= \case
        Nothing   -> (cgTerm' `mapM` IM.elems fieldsMap) >>= consStruct sret >>= \struct ->
          pure $ Struct struct (V.fromList $ getStructFieldTys (LT.typeOf struct))
        Just mask -> let -- (snd <$> foldM (maybeWriteIdx mask) (0 , sret) (IM.toList fieldsMap))
          llvmFieldTys = V.fromList (getStructFieldTys (LT.typeOf sret))
          elems = V.fromList (IM.elems fieldsMap) -- TODO norm fields

          -- ! don't store to structs, instead pass them down as retLoc
          writeField fTy sret i elem = if (isStructTy fTy || isTypeRef fTy)
            then void $ (gepTy fTy sret [constI32 0 , constI32 (fromIntegral i)] >>= setRetLoc) <* cgTerm' elem
            else cgTerm' elem >>= storeIdx fTy sret i
          go i = if i == V.length elems
            then block `named` "end"
            else let elem = elems V.! i
                     writeAlways = case elem of { Lit{} -> True ; _ -> False }
            in if writeAlways
            then mdo { writeField (llvmFieldTys V.! i) sret i elem ; br b ; b <- go (i + 1) ; pure b }
            else do
              start <- block
              yes   <- extractValue mask [fromIntegral i]
              mdo
                condBr yes next write
                write <- block
                writeField (llvmFieldTys V.! i) sret i elem
                br next
                next <- go (i + 1)
                pure start
          in Struct sret llvmFieldTys <$ go 0

-- Gmp calls
callGMPFn fnName rp args = lift (GMP.getGMPDecl fnName) >>= \f -> rp <$ f `call` map (,[]) (rp : args)
obtainRetLoc = getGMPRetPtr True >>= \rp -> rp <$ delRetLoc

emitGMPInstr :: Maybe L.Operand -> NumInstrs -> [Term] -> CGBodyEnv s L.Operand
emitGMPInstr rl i args = let
  genArgs          = cgTerm' `mapM` args
  callNoSret fnName args   = lift (GMP.getGMPDecl fnName) >>= \f -> f `call'` args
  callOp gmpFn rp = genArgs >>= callGMPFn gmpFn rp -- nothing to fold even knowing the term arguments
  zext64 = \case { Lit (Int i) -> pure (constI64 i) ; larg -> cgTerm' larg >>= zext' i64_t }
  in case i of
  IntInstr j -> obtainRetLoc >>= \rp -> case j of
    Add   -> callOp GMP.add rp
    Sub   -> callOp GMP.sub rp
    Mul   -> callOp GMP.mul rp
    Neg   -> callOp GMP.neg rp
    AbsVal-> callOp GMP.abs rp
  -- ! no retloc for these
  PredInstr j -> case j of -- these don't write to retloc, but are probably precursors to a branch
    LECmp -> genArgs >>= callNoSret GMP.cmp
      >>= \cmpRet -> emitInstr i1_t (L.ICmp IP.SLT cmpRet (constI32 0) [])

emitGMPOther rl j args = let
  callOp gmpFn rp = cgTerm' `mapM` args >>= callGMPFn gmpFn rp
  in obtainRetLoc >>= \rp -> case j of
  AddUI    -> callOp GMP.add_ui rp
  SubUI    -> callOp GMP.sub_ui rp
  UISub    -> callOp GMP.ui_sub rp
  MulSI    -> callOp GMP.mul_si rp
  MulUI    -> callOp GMP.mul_ui rp
  AddMul   -> callOp GMP.addmul rp
  AddMulSi -> callOp GMP.addmul_si rp
  SubMul   -> callOp GMP.submul rp
  SubMulSi -> callOp GMP.submul_si rp
  Mul2Exp  -> callOp GMP.mul2exp rp
  CMPUI    -> callOp GMP.cmp_ui rp
  CMPAbsD  -> callOp GMP.cmp_abs_d rp
  CMPAbsUI -> callOp GMP.cmp_abs_ui rp
  PowMUI   -> callOp GMP.powm_ui rp
  PowUI    -> callOp GMP.pow_ui rp
  UIPowUI  -> callOp GMP.ui_pow_ui rp

-- emitMatchApp args ty alts d = case args of
--   [scrutCore] -> do
--     stgScrut  <- cgTerm scrutCore
--     retTy <- lift (cgType ty)
--     let frame = fromMaybe (panic "no frame") $ fr stgScrut
--         scrut = op stgScrut
--     tag    <- load' =<< (`gep` [constI32 0]) =<< bitcast scrut (LT.ptr sumTagType)
--     -- each branch is responsible for memory, duping frames etc..
--     ourFrame <- frAlloc_isSingle frame -- TODO suspect
--     let mkAlt l e = genAlt ourFrame frame scrut l e >>= \(STGOp op maybeD) ->
--           bitcast op retTy <&> (`STGOp` maybeD)
--         branches = ("",) . uncurry mkAlt <$> (IM.toList alts)
--     mkBranchTable tag (C.Int 32 . fromIntegral <$> IM.keys alts) branches
--   bad -> panic $ "Match should have exactly 1 argument; not " <> show (length bad)

-- -- also return the args consumed (Match needs to uniformize this)
-- genAlt :: L.Operand -> L.Operand -> L.Operand -> ILabel -> Expr -> CGBodyEnv s CGOp
-- genAlt isOurFrame frame scrut lName (Core (Abs args _free t ty) _ty) = do
--   altType <- lift $ LT.ptr . LT.StructureType False . (sumTagType :) <$> (cgType `mapM` (snd <$> args))
--   e   <- bitcast scrut altType
--   llArgs <- loadIdx e `mapM` [1 .. length args]
--   let newSplit = Split lName frame (IM.fromList $ zip (LLVMOp . fst<$>args) llArgs)
--    in modifySF $ \s->s{ splits = newSplit : splits s }
-- --frAlloc_freeFrag frame e (L.ConstantOperand $ C.sizeof $ LT.typeOf e) -- TODO too early ? sometimes pointless ?
-- --frAlloc_pop frame e (L.ConstantOperand $ C.sizeof $ LT.typeOf e) -- TODO too early ? sometimes pointless ?
--   r <- cgTerm t
--   modifySF $ \x -> x { splits = drop 1 (splits x) }
--   pure r

isVoidTy x = case x of { LT.VoidType -> True ; x -> False }

cgOpInstr instr args = case instr of
  MkTop  -> pure $ L.ConstantOperand (C.Undef top_t)
  MkBot  -> pure $ L.ConstantOperand (C.Undef bot_t)
  Puts   -> lift (getPrimDecl puts)   >>= \f -> call' f args
  PutNbr -> lift (getPrimDecl printf) >>= \f -> cgTerm' (Lit (String "%d\n")) >>= (call' f . (: args))

  Zext   -> (\[a] -> zext a intType) args
  GMPPutNbr -> (\[i] -> GMP.putNbr i) args
  GMPZext p -> getGMPRetPtr False >>= \retLoc -> let i = (\[a] -> a) args in case compare p 64 of
        LT -> zext i i64_t >>= \i' -> GMP.zext2GMP i' retLoc
        EQ -> GMP.zext2GMP i retLoc
        GT -> panic "converting integer greater than 64 bits to gmp"
  CallExt nm -> let
    fn = C.GlobalReference (LT.ptr $ LT.FunctionType intType [] True) (L.mkName (T.unpack nm))
    in call' (L.ConstantOperand fn) args

  i -> let instr = primInstr2llvm i in case (i , args) of
      (NumInstr (PredInstr _) , [a,b]) -> emitInstr boolType (instr a b)
      (_ , [a,b]) -> emitInstr (LT.typeOf a) (instr a b)
      x -> panic $ "arity mismatch on prim instruction: " <> show i

-- some instrs benefit from inspecting term arguments
cgInstrApp rl instr args = case instr of
  MkPAp n -> (cgTerm `mapM` args) <&> \case -- args of -- is n of any use ?
    f : cgargs -> case f of
      FunctionOp ~fptr free at rt -> PapOp f cgargs
      PapOp fn captures -> PapOp fn (captures ++ cgargs)
    _ -> error "TODO codegen partial application"
  instr -> LLVMOp <$> case instr of
    PutNbr | [Lit (Int i)] <- args -> cgTerm' (Lit (String (show i))) >>= cgOpInstr Puts . (:[])
    Zext   | [Lit (Int i)] <- args -> pure $ constI64 i
    GMPInstr i  -> emitGMPInstr rl i args
    GMPZext p -> case args of
      [Lit (Int i)] -> (getGMPRetPtr False >>= GMP.initGMPInt i)
      [x] -> cgTerm' x >>= \i -> getGMPRetPtr False >>= \retLoc -> case compare p 64 of
        LT -> zext i i64_t >>= \i' -> GMP.zext2GMP i' retLoc
        EQ -> GMP.zext2GMP i retLoc
        GT -> panic "converting integer greater than 64 bits to gmp"
    i -> cgTerm' `mapM` args >>= cgOpInstr i

mkIf ifE thenE elseE = (getRetLoc <* delRetLoc) >>= \rl -> cgTerm' ifE >>= \scrut -> let
  -- if a subexpression didn't copy to the retloc, we need to do it
  copyIfRl struct = getRetLoc >>= maybe (pure ()) (\rl -> load' struct >>= store' rl)
  in mdo
  setRetLocM rl
  condBr scrut yes no
  yes  <- block `named` "yes"
  ifOp <- cgTerm' thenE
  copyIfRl ifOp
  br res

  no     <- block `named` "no"
  elseOp <- cgTerm' elseE
  copyIfRl elseOp
  br res

  res <- block `named` "phi"
  LLVMOp <$> phi [(ifOp , yes) , (elseOp , no)]

--mkBranchTable scrut [C.Int 1 1 , C.Int 1 0] (zip ["then","else"] [cgTerm thenE, cgTerm elseE])
--mkMultiIf ((ifE,thenE):alts) elseE = genSwitch ifE [(C.Int 1 1 , thenE)] . Just =<< case alts of
--    []       -> pure elseE
--    branches -> mkMultiIf branches elseE

-- genSwitch :: Term -> [(C.Constant , Term)] -> Maybe Term -> CGBodyEnv s L.Operand
-- genSwitch scrutTerm branches defaultBranch = let
--   callErrorFn str = _ -- call (errFn str) [] <* unreachable
--   genAlt endBlock (scrutVal , expr) = do -- collect (result,block) pairs for the phi instr
--     flip (,) <$> block <*> (cgTerm' expr <* br endBlock)
--   in mdo
--   scrut <- cgTerm' scrutTerm
--   switch scrut dBlock (zip (fst <$> branches) (snd <$> retBlockPairs))
--   dBlock   <- (block `named`"switchDefault")
--   dSsa   <- case defaultBranch of
--     Just d  -> cgTerm' d <* br endBlock
--     Nothing -> callErrorFn "NoPatternMatch"
--   retBlockPairs <- genAlt endBlock `mapM` branches
--   endBlock <- block `named` "switchEnd"
--   phi $ (dSsa, dBlock) : retBlockPairs
