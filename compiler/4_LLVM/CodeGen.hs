module CodeGen (mkStg) where
import Prim
import Prim2LLVM
--import Externs
import CoreSyn
import CoreUtils
import qualified GMPBindings as GMP
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.Text as T
import qualified Data.IntMap as IM
import qualified Data.Map as M
import           Data.List ((!!)) -- thanks llvm-hs
import qualified Data.String
import qualified LLVM.AST as L
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.FunctionAttribute as FA
import qualified LLVM.AST.Type  as LT
import qualified LLVM.AST.Typed as LT
import qualified LLVM.AST.ParameterAttribute as LP
import           LLVM.AST.Global
import           LLVM.AST.Linkage as L
--import qualified LLVM.AST.IntegerPredicate as IP
--import           LLVM.AST.CallingConvention as CC
import LLVM.IRBuilder.Monad
import LLVM.IRBuilder.Instruction as LIR hiding (gep)

--mkStg :: V.Vector Expr -> V.Vector (HName , Bind) -> V.Vector QTT -> L.Module
mkStg externBindings coreMod@(JudgedModule modName bindNames coreBinds) = let
  mkVAFn ty nm = L.GlobalDefinition functionDefaults
    { name = L.mkName nm , linkage = L.External , parameters=([],True) , returnType = ty }
  nBinds = V.length coreBinds
  moduleDefs = runST $ do
    v <- V.unsafeThaw (TWIP <$> V.zip bindNames coreBinds)
    st <- execStateT (cgBind `mapM` [nBinds-1 , nBinds-2 .. 0]) CGState {
        wipBinds = v
--    , externResolver = extResolver
      , gmpDecls  = Nothing
      , primDecls = Nothing
      , externs  = externBindings
      , coreModule = coreMod
      , llvmDefs = [
          L.TypeDefinition "A"   Nothing
        , L.TypeDefinition "Void"Nothing
        , L.TypeDefinition "Bot"Nothing
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
    pure $ primDecls ++ gmpDecls ++ llvmDefs st
  in L.defaultModule {
      L.moduleName        = Data.String.fromString $ T.unpack modName
    , L.moduleDefinitions = moduleDefs
--  , L.moduleTargetTriple = Just "x86_64-unknown-linux-gnu" -- x86_64-pc-linux-gnu
--  , L.moduleDataLayout = Just "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
    }

-- Bindings vary from functions to types to constants to constexprs to instructions
-- maybe use llvm.global_ctors: appending global [n x { i32, void ()*, i8* }]
cgBind :: IName -> CGEnv s StgWIP
cgBind i = gets wipBinds >>= \wip -> MV.read wip i >>= \case
 TWIP (nm , bind) -> let
   llvmNm = L.mkName (T.unpack nm) -- bit sad llvm..
   in mdo -- handle recursive refs using MonadFix
     MV.write wip i b
     b <- case bind of
       BindOK tt -> case tt of
         Core (Instr instr) ty -> STGFn RetReg [] <$> emitPrimFunction instr [intType , intType] intType
         Core (Abs args free t _ty) ty -> let
           (argTys , retTy) = getArrowArgs ty
           as = zipWith (\(i,_) t -> (i,t)) args argTys
           in dataFunction llvmNm as [] t retTy [] -- TODO fragile (paps ? etc..)
         Core t ty -> dataFunction llvmNm [] [] t ty [] -- <&> \case { STGFn _ [] op -> STGConstant op ; f -> f }
         PoisonExpr -> panic $ "attempted to codegen a poison expr: " <> nm
         Ty ty -> LLVMTy <$> cgType ty
       ko -> panic $ "panic Core failed to generate a valid binding: " <> nm
     pure b
 x -> pure x

-- DataFunctions pass extra frame arguments with their data args
dataFunction :: L.Name -> [(IName, [TyHead])] -> [(IName , LT.Type)]
  -> Term -> [TyHead] -> [FA.FunctionAttribute]
  -> CGEnv s StgWIP
dataFunction llvmNm args free body returnType attribs = let
    iArgs = fst<$>args ; iFree = fst<$>free
    retKind  = dataRetKind ((\[x] -> x) returnType)
    isDataTy = any isDataTyHead
    retData  = isDataTy returnType
    rArgs = args
    mkTyconPtr t = case t of -- tycon Function arguments are always pointers (can annotate with byval)
      LT.StructureType{} -> LT.ptr t
      LT.NamedTypeReference{} -> LT.ptr t
      t -> t
  in do
  retTy   <- cgType returnType -- !! possibly raw struct
  let retDropFieldsTy = LT.ArrayType (fromIntegral $ length (getStructFieldTys retTy)) i1_t
  rArgTys <- (fmap mkTyconPtr . cgType . snd) `mapM` rArgs --dArgTys <- (cgType . snd) `mapM` dArgs

  ((retTy , fnParams) , blocks) <- runIRBuilderT emptyIRBuilder $ do
    (retPtr , rd) <- case retData of
      False -> pure (Nothing , Nothing)
      True  -> do
        rp <- Just . L.LocalReference (LT.ptr retTy)  <$> fresh
        rd <- Just . L.LocalReference retDropFieldsTy <$> fresh
        pure (rp , rd)
    rParams <- rArgTys `forM` \ty -> L.LocalReference ty <$> fresh

    modify $ \x -> x { stack = CallGraph
     { regArgs  = IM.fromList$zip (fst<$>rArgs) rParams
     , splits      = []
     , retLoc      = retPtr
     , dynRetDrops = rd
     } : stack x }
    cgTerm' body >>= \sret -> if retData then retVoid else ret sret
    modify $ \x -> x { stack = drop 1 (stack x) }

    let mkParam attrib = (\(L.LocalReference ty nm) -> Parameter ty nm attrib)
        fnParams = mkParam [] <$> rParams
    -- llvm: "functions with sret must return void", for abi compatibility:
    -- The x86-64 ABIs require byval struct returns be copied into %rax|%eax
    pure $ case (retPtr , rd) of
      (Just sret , Just rd) -> (LT.VoidType , mkParam [LP.SRet] sret : mkParam [] rd : fnParams)
      _         -> (retTy , fnParams)

  STGFn retKind iFree <$> emitFunction llvmNm fnParams retTy blocks

cgTerm' = fmap op . cgTerm

accessField r i t = if isStructPtr t then gep r [constI32 0 , constI32 $ fromIntegral i] else loadIdx r i

getGMPRetPtr :: CGBodyEnv s L.Operand
getGMPRetPtr = let
  initGMP = do
    r <- alloca' GMP.mpz_struct_tname Nothing --GMP.mpz_struct_t Nothing >>= bitcast' GMP.mpz_t
--  (lift (GMP.getGMPDecl GMP.init) >>= \f -> f `call'` [r])
    pure r
  in getRetLoc >>= maybe initGMP pure --(bitcast' GMP.mpz_t)

cgTerm :: Term -> CGBodyEnv s CGOp
cgTerm = let
  cgName = \case
    VBind i -> lift (cgBind i) >>= \case
      STGConstant x -> _--mkSTGOp <$> x `call'` []
      f -> pure $ mkSTGOp $ fnOp f
    -- Args: 1. regular args 2. dataArgs 3. splits from Match
    VArg  i -> getSF >>= \cg -> case (regArgs cg IM.!? i) of
      Just reg -> pure $ mkSTGOp reg
      Nothing  -> let
        doSplit s = (\op -> (sframe s , op)) <$> (components s IM.!? i)
        in case asum (doSplit <$> splits cg) of
        Just (f , o)  -> pure $ LLVMOp o --STGOp o (Just f) Nothing
        Nothing -> panic $ T.pack $ "arg not in scope: " ++ show i
    VExt  i -> _
  -- record field access (avoid loading inline structs)
  tyOfStructIdx i = \case
    LT.PointerType (LT.StructureType _ elems) _ -> if length elems <= i
      then error $ "index too large: " <> show i <> " ! " <> show elems else elems !! i
    x -> error $ "expected struct type :" <> show x

  in \x -> case x of
  Var vNm     -> cgName vNm
  Lit (Int i) -> pure $ mkSTGOp (constI32 i)
  Lit l   -> mkSTGOp . L.ConstantOperand <$> lift (literal2Stg l)
  Instr i -> error $ show i -- cgPrimInstr i -- TODO get/emit wrapper fn for instr
  Abs args free t ty -> lift $ freshTopName "lam" >>= \nm ->
    mkSTGOp . fnOp <$> dataFunction nm args [] t ty []
--MultiIf -> mkMultiIf ifsE elseE
  Label i tts      -> _
  List  args       -> _
  m@(Match ty labels d) -> panic $ "floating match" -- cgTerm (Abs .. ) fresh arginames somehow

  Cons fields      -> mkRecord fields

  -- Note. the record in question will be already casted (ie. address resolved | copied iff lensOver changes a field's size)
  TTLens tt fields lens -> mkSTGOp <$> do
   getRetLoc >>= \sret -> case lens of
    LensGet -> cgTerm' tt >>= \struct -> gep struct [constI32 0 , constI32 0] >>= \loc ->
      if isStructPtr (LT.typeOf loc) then pure loc else load' loc
    LensOver (asmIdx,_) (Core fn _fnty) -> delRetLoc *> cgTerm' fn >>= \f -> cgTerm' tt >>= \struct -> do
      loc <- gep struct [constI32 0 , constI32 $ fromIntegral asmIdx]
      sretLeaf <- gep (fromMaybe (panic "no sret !!") sret) [constI32 0 , constI32 0]
      if isStructPtr (LT.typeOf loc)
      then void $ call' f [sretLeaf , loc]
      else load' loc >>= \arg -> call' f [arg] >>= store' sretLeaf
      pure struct
    LensSet t -> error $ show lens

  Cast cast term -> mkSTGOp <$> doCast cast term

  App f args -> cgApp f args
  x -> error $ "MkStg: not ready for term: " <> show x

getStructFieldTys = \case
  LT.StructureType _ elems -> elems
  LT.PointerType s _       -> getStructFieldTys s
  x -> error $ "expected struct type, got: " <> show x

getFnSRetTy fn = let -- probably dumb
  getFn = \case
    LT.FunctionType ret ars va -> ars
    LT.PointerType (LT.FunctionType ret ars va) _ -> ars
    x -> panic $ "expected function type: " <> show x
  in (\(Just (LT.PointerType r _)) -> r) . head $ getFn (LT.typeOf fn)

productCast2dropMarkers :: Int -> [(ASMIdx , BiCast)] -> (Int , [Int])
productCast2dropMarkers drops leafCasts = let -- mark dropped fields
  go (asmIdx , _) (len , acc) = (\next -> (1+len , next : acc)) $ if asmIdx == len then 0 else 1
  in foldr go (0 , []) leafCasts

cgApp f args = case f of
  Match ty alts d -> _ --emitMatchApp args ty alts d
  Instr i   -> case i of -- ifThenE is special since it can return data
    IfThenE -> case args of { [ifE, thenE, elseE] -> mkIf ifE thenE elseE }
    _ -> mkSTGOp <$> cgInstrApp i args
  Var (VBind fI) -> lift (cgBind fI) >>= \case
    STGFn retData free fptr -> do
      rl <- getRetLoc
      delRetLoc
      mkSTGOp <$> case retData of
        RetReg    -> cgTerm' `mapM` args >>= \stgops -> call' fptr stgops
        RetBigint -> cgTerm' `mapM` args >>= \stgops -> call' fptr =<< (:stgops) <$> getGMPRetPtr
        RetRecord -> case args of
          [Cast (CastProduct drops leafCasts) prodArg] -> do
            stgops <- cgTerm' `mapM` args
            setRetLocM rl
            callRecordFn (productCast2dropMarkers drops leafCasts) _super _sRetTy fptr stgops
          x -> error $ show x
  Var (VArg fI) -> gets (mkSTGOp . fromMaybe (panic $ "arg not found: " <> show fI) . (IM.!? fI) . regArgs . fromJust . head . stack)
  Var (VExt fI) -> _
  f -> panic $ "STG: floating function; expected binding index: " <> show f
--f -> cgTerm f >>= \f' -> call' f' =<< (cgTerm `mapM` args)

recordApp prodCast f args = getRetLoc >>= \sret -> delRetLoc *> do
  fn   <- cgTerm' f
  args <- cgTerm' `mapM` args
  case prodCast of
    BiEQ -> _
    CastProduct drops fields -> let
        sretTy = getFnSRetTy fn
        fTys = V.fromList $ getStructFieldTys sretTy
        castStructElems = (\(asmIdx , cast) -> fTys V.! asmIdx) <$> fields
        castStruct = LT.StructureType False castStructElems
      in do
      setRetLocM sret
--    castFn <- bitcast fn (LT.ptr $ LT.FunctionType (LT.ptr castStruct) [] True) -- TODO preferably bitcast to the right type
      r <- callRecordFn (productCast2dropMarkers drops fields) sretTy castStruct fn args
      doProductCast (zipWith (\i (castI , l) -> (i,l)) ([0..]::[Int]) fields) r -- TODO admittedly not great

getCastRetTy ty = \case
  CastInstr GMPZext{} -> GMP.mpz_struct_tname
  BiEQ -> ty
  x -> error $ "not done yet: " <> show x

doCast cast term = let
  prodCast leaves term = case term of
    App f args      -> recordApp cast f args
    f@(Var VBind{}) -> recordApp cast f [] -- ie. dodge args / intermediates
    _ -> cgTerm' term >>= doProductCast leaves
  in case cast of
  BiEQ                     -> cgTerm' term
  CastInstr i              -> cgInstrApp i [term]
  CastProduct drops leaves -> prodCast leaves term

doProductCast [(idx , BiEQ)] r = pure r
doProductCast leaves r = let
  inlineStructTy t = case t of { LT.PointerType s _ | isStructTy s ->  s ; t -> t }
  fTys = inlineStructTy <$> V.fromList (getStructFieldTys (LT.typeOf r))
  castStructElems = (\(asmIdx , leafCast) -> fTys V.! asmIdx) <$> leaves

  readField sret r retIdx (fTy , (leafIdx , leafCast)) = do
      leafPtr <- gep r [constI32 0 , constI32 $ fromIntegral leafIdx]   `named` "leafPtr"
      let leafStruct = isStructTy $ (\(LT.PointerType s _) -> s) $ LT.typeOf leafPtr
          retStruct  = isStructTy $ (\(LT.PointerType s _) -> s) $ LT.typeOf sret
      if retStruct
      then gep sret [constI32 0 , constI32 $ fromIntegral retIdx] `named` "retloc" >>= setRetLoc
      else setRetLoc sret
      leaf   <- if leafStruct then pure leafPtr else load' leafPtr
      casted <- doCastOp leafCast leaf
      unless retStruct (store' sret casted)

  subCastStruct = LT.StructureType False (zipWith getCastRetTy castStructElems (snd <$> leaves))
  in mdo
  sret <- getRetLoc >>= maybe (alloca' subCastStruct Nothing `named` "castRecord") (bitcast' (LT.ptr subCastStruct))
  zipWithM (readField sret r) ([0..]::[Int]) (zip castStructElems leaves)
  pure sret

doCastOp :: BiCast -> L.Operand -> CGBodyEnv s L.Operand
doCastOp cast operand = case cast of
  BiEQ        -> pure operand
  CastInstr i -> cgOpInstr i [operand]

callRecordFn (fieldCount , dropMarkers) superType ty fn args = let
  maskTy = LT.ArrayType (fromIntegral fieldCount) i1_t
  arr    = L.ConstantOperand (C.Array i1_t (C.Int 1 . fromIntegral <$> dropMarkers))
--count fn  = let go i = \case { []->i ; x:xs | fn x -> go (1+i) xs ; _->i} in go 0
--skipFront = count (== 1) dropMarkers
--mkRecordSRet ty = (retLoc <$> getSF) >>= let
--  in \case
--  Just sret -> sret <$ storePtr maskTy sret arr
--  Nothing   -> do
--    sret <- alloca' {-ty-}superType Nothing `named` "localSRet"
--    sret <$ storePtr maskTy sret arr
  mkRecordSRet = getRetLoc >>= maybe (alloca' superType Nothing `named` "localSRet") pure
  in mkRecordSRet >>= \sret -> sret <$ call' fn (sret : arr : args)

--in mkRecordSRet ty >>= \sret -> call' fn . (sret : args)

-- & takeArg : write an arg tycon into sret (caller should copy if needed)
-- + sort both records into sret
-- = when sret==arg , can avoid copying fields
-- - don't write all fields (*sret as bitmask)
mkRecord :: IM.IntMap Term -> CGBodyEnv s CGOp
mkRecord fieldsMap = let
  fLen = IM.size fieldsMap -- TODO this is O(n) !
  in (getRetLoc <* delRetLoc) >>= \case
    Nothing   -> (cgTerm' `mapM` IM.elems fieldsMap) <&> \fs -> RawStruct (V.fromList fs)
    Just sret -> let -- spawn a struct , don't write to subcasted fields
--    next (LT.PointerType (LT.StructureType x v) a) = let
--      tys = drop 1 v -- of { [t] -> [t , i8_t] ; x -> x } -- dummy value at end of struct
--      in LT.PointerType (LT.StructureType x tys) a
      maybeWriteIdx mask (idx , sret) (coreFName , term) = let
        lastElem = idx + 1 == fLen
        initIfGMP ty sret = sret <$ case ty of
          LT.NamedTypeReference "mpz_struct_t" -> GMP.initSRetGMP sret
          _ -> pure _
        in mdo
        br start
        start <- block `named` "start"
--      skip  <- bitcast' (next (LT.typeOf sret)) sret
        yes   <- extractValue mask [fromIntegral idx]
        condBr yes end write

        write <- (block `named` "writeField")
        case LT.typeOf sret of -- write result directly to the struct
          LT.PointerType (LT.StructureType _ (x : xs)) _ | isStructTy x ->
            (bitcast' (LT.ptr x) sret >>= initIfGMP x >>= void . setRetLoc) <* cgTerm term
          _ -> cgTerm' term >>= storeIdx sret idx
--      -- gep to end of this field for next writes
--      nextSRet <- if lastElem -- avoid indexing past last elem
--        then pure (mkNullPtr (LT.ptr (LT.StructureType False [])))
--        else gep sret [constI32 0 , constI32 1] >>= bitcast' (next (LT.typeOf sret))
        writeEnd <- currentBlock
        br end

        end  <- (block `named` "join")
        pure (1 + idx , sret)
        -- final phi is useless else (1 + idx ,) <$> phi [(nextSRet , writeEnd) , (skip , start)]

      in do
      dynRetDrops <$> getSF >>= \case
        Nothing   -> (cgTerm' `mapM` IM.elems fieldsMap) >>= consStruct sret >>= \struct ->
          pure $ Struct (V.fromList $ getStructFieldTys (LT.typeOf struct)) struct
        Just mask -> let -- (snd <$> foldM (maybeWriteIdx mask) (0 , sret) (IM.toList fieldsMap))
          v = V.fromList (IM.elems fieldsMap) -- TODO norm fields
          go i = if i == V.length v then block `named` "end"
            else mdo
              start <- block
              yes   <- extractValue mask [fromIntegral i]
              condBr yes next write
              write <- block
              (cgTerm' (v V.! i) >>= storeIdx sret i)
              br next
              next <- go (i+1)
              pure start
          in mdo
            br start
            start <- go 0
            pure $ Struct _ sret
emitGMPInstr :: NumInstrs -> [Term] -> CGBodyEnv s L.Operand
emitGMPInstr i args = let
  genArgs     = cgTerm' `mapM` args
  callGMPFn fnName rp args = lift (GMP.getGMPDecl fnName) >>= \f -> rp <$ f `call` map (,[]) (rp : args)
  callOp gmpFn rp = genArgs >>= callGMPFn gmpFn rp -- nothing to fold even knowing the term arguments
  in getGMPRetPtr >>= \rp -> delRetLoc *> case i of
  IntInstr j -> case j of
    Add   -> let
      addUI a b = cgTerm' a >>= \larg-> cgTerm' b >>= zext' i64_t >>= \rarg-> callGMPFn GMP.add_ui rp [larg , rarg]
      in case args of
        [Cast (CastInstr (GMPZext i)) larg , rarg] -> addUI rarg larg
        [larg , Cast (CastInstr (GMPZext i)) rarg] -> addUI larg rarg
        _ -> callOp GMP.add rp
    Sub   -> callOp GMP.sub rp
    Mul   -> callOp GMP.mul rp
    Neg   -> callOp GMP.neg rp
    AbsVal-> callOp GMP.abs rp

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

-- also return the args consumed (Match needs to uniformize this)
genAlt :: L.Operand -> L.Operand -> L.Operand -> ILabel -> Expr -> CGBodyEnv s CGOp
genAlt isOurFrame frame scrut lName (Core (Abs args _free t ty) _ty) = do
  altType <- lift $ LT.ptr . LT.StructureType False . (sumTagType :) <$> (cgType `mapM` (snd <$> args))
  e   <- bitcast scrut altType
  llArgs <- loadIdx e `mapM` [1 .. length args]
  let newSplit = Split lName frame (IM.fromList $ zip (fst<$>args) llArgs)
   in modifySF $ \s->s{ splits = newSplit : splits s }
--frAlloc_freeFrag frame e (L.ConstantOperand $ C.sizeof $ LT.typeOf e) -- TODO too early ? sometimes pointless ?
--frAlloc_pop frame e (L.ConstantOperand $ C.sizeof $ LT.typeOf e) -- TODO too early ? sometimes pointless ?
  r <- cgTerm t
  modifySF $ \x -> x { splits = drop 1 (splits x) }
  pure r

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

cgOpInstr instr args = case instr of
  MkTop  -> pure $ L.ConstantOperand (C.Undef top_t)
  MkBot  -> pure $ L.ConstantOperand (C.Undef bot_t)
  Puts   -> lift (getPrimDecl puts)   >>= \f -> call' f args
  PutNbr -> lift (getPrimDecl printf) >>= \f -> cgTerm' (Lit (String "%d\n")) >>= (call' f . (: args))

  Zext   -> (\[a] -> zext a intType) args
  GMPPutNbr -> (\[i] -> GMP.putNbr i) args
  GMPZext p -> let i = (\[a] -> a) args in case compare p 64 of
        LT -> zext i i64_t >>= \i' -> (getGMPRetPtr >>= GMP.zext2GMP i')
        EQ -> getGMPRetPtr >>= GMP.zext2GMP i
        GT -> panic "converting integer greater than 64 bits to gmp"
  CallExt nm -> let
    fn = C.GlobalReference (LT.ptr $ LT.FunctionType intType [] True) (L.mkName (T.unpack nm))
    in call' (L.ConstantOperand fn) args

  i -> let instr = primInstr2llvm i in case (i , args) of
      (NumInstr (PredInstr _) , [a,b]) -> emitInstr boolType (instr a b)
      (_ , [a,b]) -> emitInstr (LT.typeOf a) (instr a b)
      x -> panic $ "arity mismatch on prim instruction: " <> show i

-- some instrs benefit from inspecting term arguments
cgInstrApp instr args = case instr of
--  PutNbr -> call (L.ConstantOperand (C.GlobalReference (LT.ptr $ LT.FunctionType intType [] True) (L.mkName "printf"))) =<< (map (,[]) <$> cgTerm' `mapM` (Lit (String "%d\n") : args))
    GMPInstr i  -> emitGMPInstr i args --cgTerm `mapM` args >>= \args' -> mkSTGOp <$> emitGMPInstr i (op<$>args')
    GMPZext p -> case args of
      [Lit (Int i)] -> (getGMPRetPtr >>= GMP.initGMPInt i)
      [x] -> cgTerm' x >>= \i -> case compare p 64 of
        LT -> zext i i64_t >>= \i' -> (getGMPRetPtr >>= GMP.zext2GMP i')
        EQ -> getGMPRetPtr >>= GMP.zext2GMP i
        GT -> panic "converting integer greater than 64 bits to gmp"
    i -> cgTerm' `mapM` args >>= cgOpInstr i

mkIf ifE thenE elseE = cgTerm' ifE >>= \scrut ->
  mkBranchTable scrut [C.Int 1 1 , C.Int 1 0] (zip ["then","else"] [cgTerm thenE, cgTerm elseE])
--mkMultiIf ((ifE,thenE):alts) elseE = genSwitch ifE [(C.Int 1 1 , thenE)] . Just =<< case alts of
--    []       -> pure elseE
--    branches -> mkMultiIf branches elseE

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
