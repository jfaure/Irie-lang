-- {-#LANGUAGE Strict#-}
-- core2Stg
-- * all LBinds must have a type annotation
-- * all types must be monotypes
-- * this function should never fail
--
-- ? how to make dependent types static by this point ?
-- ? also type functions etc..
module Core2Stg (core2stg)
where
import Debug.Trace

import Prim
import CoreSyn
import StgSyn
import qualified CoreUtils as CU

import Data.Char (ord)
import qualified Data.Text as T
import qualified Data.Text.Read as TR
import qualified Data.Vector as V
import qualified LLVM.AST as L -- (Operand, Instruction, Type, Name, mkName)
--import GHC.Word
import qualified LLVM.AST  -- (Operand, Instruction, Type, Name, mkName)
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.FloatingPointPredicate as FP
import qualified LLVM.AST.Type as LT
import qualified LLVM.AST.Float as LF
import           LLVM.AST.AddrSpace
import qualified Data.IntMap as IM
import Data.List

-- map for dynamic types: types created in tyjudge
type DynTyMap = TypeMap

-- TODO filter all functions from CoreModule.bindings
core2stg :: CoreModule -> StgModule
core2stg cm@(CoreModule hNm algData coreBinds nTopBinds overloads defaults _ tyConInsts _ _) =
  let (normalData, stgTypedefs) = convData algData tyConInsts
      getDynInst i conIdx = case named (tyConInsts V.! i) of
        Nothing -> error "impossible"
        Just  h -> h
  in StgModule {
     stgData  = normalData
   , typeDefs = V.fromList stgTypedefs
   , binds    = doBinds getDynInst coreBinds nTopBinds algData tyConInsts overloads
  }

doExtern :: TypeMap -> DynTyMap -> IName -> Entity -> StgBinding
doExtern tyMap dynTyMap iNm (Entity (Just nm) ty _) =
  let stgId      = convName iNm (Just nm)
  in StgBinding stgId $ case convTy tyMap dynTyMap ty of
    StgLlvmType llvmFnTy -> StgExt llvmFnTy
    t ->                    StgExtComplex t

-- handle the algData TypeMap (NameMap Entity)
-- This returns the TyAliases monotyDatas
convData :: TypeMap -> DynTyMap -> (V.Vector StgData, [(StgId, StgType)])
convData tyMap dynTyMap = mkLists $ foldr f ([],[]) (tyMap V.++ dynTyMap)
  where
  mkLists (a,b) = (V.fromList a, b)
  f (Entity (Just hNm) ty _) (d, a) = 
    let nm = LLVM.AST.mkName (CU.hNm2Str hNm)
    in case ty of
      TyPoly (PolyData ty dataDef) ->
        let (newData, subTys) = convDataDef tyMap dynTyMap dataDef
        in  (newData : d, subTys ++ a)
      -- ignore tycon defs
      TyFn{} -> (d , a)
      rawTy -> (d, (nm, convTy tyMap dynTyMap rawTy):a)
  f (Entity Nothing ty _) (d,a) = case ty of
    TyRigid i -> (d , (convName i Nothing , StgPolyType) : a)
    _ -> (d,a)
--f o (d,a) = error $ show o ++ " :" ++ show d ++ " , " ++ show a

convDataDef :: TypeMap -> DynTyMap -> DataDef
            -> (StgData, [(StgId, StgType)])
convDataDef tyMap dynTyMap (DataDef dataNm sumAlts) = let
  deref      = (tyMap V.!)
  mkStgId    = LLVM.AST.mkName . CU.hNm2Str
  mkProdData (pNm, tys)
    = StgProductType (mkStgId pNm) $ convTy tyMap dynTyMap <$> tys
  sumTy      = StgSumType (mkStgId dataNm) $ mkProdData <$> sumAlts
  qual       = dataNm `T.snoc` '.'
  subAliases = (\(pNm, tys) -> mkStgId $ qual `T.append` pNm) <$> sumAlts
  in  (sumTy, zip subAliases (repeat $ StgTypeAlias $ mkStgId dataNm))

-- needs the TypeMap in order to deref types
convTy :: TypeMap -> DynTyMap -> Type -> StgType
convTy tyMap dynTyMap =
  let deref   = (tyMap V.!)
      convTy' = convTy tyMap dynTyMap
      mkAlias iNm = convName iNm (named (deref iNm))
  in \case
  TyAlias iNm ->
    let tyInfo  = deref iNm
        stgAlias = convName iNm (named tyInfo)
    in case typed tyInfo of
      -- polytypes will need to be bitcasted in llvm
      TyPoly (PolyJoin{}) -> StgPolyType
      TyPoly PolyAny       -> StgPolyType
--    TyMono (MonoRigid ri) -> StgRigid ri
      o                    -> StgTypeAlias stgAlias
  TyArrow types       -> StgFnType (convTy' <$> types)
  TyMono m            -> case m of
    MonoTyPrim prim -> StgLlvmType $ primTy2llvm prim
--  MonoRigid  riNm -> StgRigid riNm -- arguments of tycons
    MonoSubTy  r p ci -> convTy' (TyAlias p) --StgPolyType $ mkAlias r

  TyFn args val -> error ("tycon definition")
--    TyApp       ty args  -> StgTyCon (convTy' ty) (convTy' <$> args)
--    TyDependent args expr-> error ("dependent type: " ++ show tyfun)
  TyRigid{}    -> StgPolyType
  t@(TyCon ty tys) -> StgPolyType --convTy' $ head tys --error $ show t

  TyInstance ty inst -> case inst of
    TyArgInsts tys -> convTy' ty
    TyPAp t1s t2s ->
      let st1s = convTy' <$> t1s
          st2s = convTy' <$> t2s
      in StgPApTy st1s st2s
    TyOverload fId       -> convTy' ty
    TyDynInstance fId conIdx -> StgTypeAlias
      $ convName (fId + V.length tyMap) (named (dynTyMap V.! fId))

  TyPoly (PolyJoin alts) -> StgPolyType -- error $ "core2stg: polyunion: " ++ show alts -- convTy' $ head alts
  TyPoly (PolyAny) -> StgPolyType
  -- Note any other type is illegal at this point
  t -> error ("internal error: core2Stg: not a monotype: " ++ show t)

-- the V.imap will give us the right inames since it contains all terms
doBinds :: (Int->Int->HName) -> V.Vector Binding -> Int
        -> TypeMap -> DynTyMap -> V.Vector ClassDecl
        -> V.Vector StgBinding
doBinds getDynInst binds nTopBinds tyMap dynTyMap classDecls
  = V.fromList $ V.ifoldr f [] binds --(V.take nTopBinds binds)
  where
  convTy'      = convTy tyMap dynTyMap
  lookupBind i = CU.lookupBinding i binds
  lookupTy     = typed . (tyMap V.!)
  unVar        = CU.unVar tyMap -- \case { TyAlias i->lookupTy i ; t -> t}
  convName' i  = convName i $ named $ info $ lookupBind i
  convExpr'    = convExpr binds tyMap classDecls getDynInst lookupTy
  f iNm        = \case
    LBind _ _ Lit{} -> id
    LBind info args expr -> let
      nm       = convName iNm (named info)
      argNames = StgVarArg . convName' <$> args
      (argTys, [retTy]) = case typed info of
          TyArrow tys -> splitAt (length tys-1) $ tys
          t -> ([], [t])
      stgArgTys = convTy' <$> argTys
      stgRetTy  = convTy' retTy
      rhs = StgTopRhs argNames stgArgTys stgRetTy $ convExpr' retTy expr
      in (StgBinding nm rhs :)
    Inline{}   -> id
    LInstr{}   -> id
    LExtern ty -> (doExtern tyMap dynTyMap iNm ty :) -- id
    LArg{}     -> id
    LCon{}     -> id
    LClass{}   -> id
    LTypeVar e -> error $ "tyVar: " ++ show e
--  wht -> error $ show wht

convExpr :: BindMap -> TypeMap -> V.Vector ClassDecl
         -> (IName->IName->HName) -> (ITName -> Type)
         -> Type -> CoreExpr
         -> StgExpr
convExpr bindMap tyMap classDecls getDynInst lookupTy ty =
 let lookup      = (bindMap V.!)
     convExpr''  = convExpr bindMap tyMap classDecls getDynInst lookupTy
     convExpr'   = convExpr'' ty
     convName' i = convName i $ named $ info $ lookup i
     typeOf      = typed . info . lookup
     unVar       = CU.unVar tyMap
 in \case
 Var nm -> case lookup nm of
   Inline i e -> convExpr' e
   LBind i _ l@Lit{} -> convExpr'' (typed i) l
   _ -> StgLit $ StgVarArg $ convName' nm
 Lit lit -> StgLit $ StgConstArg $ typedLit2Stg lit (unVar $ ty)
            -- StgLit $ StgConstArg $ literal2Stg lit
 -- App: need to check the retTy for instantiation markers
 Instr MkNum  [n] -> convExpr'' ty n
 Instr MkReal [n] -> convExpr'' ty n
 -- ! shares logic with App
 Instr x args ->
   let mkStgExprArg t x = StgExprArg $ convExpr'' t x
   in  StgInstr (prim2llvm x)
       $ (zipWith mkStgExprArg (repeat ty) args) -- TODO repeat
 App fId args ->
   let fnTy = typed $ info $ lookup fId
       (argTys, [retTy]) = case fnTy of
         TyArrow tys -> splitAt (length tys-1) $ tys
         TyFn _ (TyArrow tys) ->
           splitAt (length tys-1) tys
         t -> ([], [t])
       arity = length args
       tyArity = length argTys

       -- TODO temp hack since VarArgs functions short the zipWith
       argTys' = argTys ++ repeat TyUnknown
       mkStgExprArg t x = StgExprArg $ convExpr'' t x
       stgArgs = zipWith mkStgExprArg argTys' args
   in case ty of
     TyInstance ty inst -> case inst of
       TyArgInsts tys ->
         let instArgs = zipWith mkStgExprArg tys args
         in StgApp (convName' fId) instArgs
       TyOverload instId -> -- TODO temp hack (repeat ty)
         let instArgs = zipWith mkStgExprArg (repeat ty) args
         in case lookup instId of
           LInstr i instr -> convExpr'' ty (Instr instr args)
           _ -> StgApp (convName' instId) instArgs
       TyDynInstance i conIdx ->
         StgApp (convName i (Just $ getDynInst i conIdx)) stgArgs
       TyPAp{}-> StgInstr (StgPApApp (trace "careful"$arity-tyArity))
                  $ StgVarArg (convName' fId) : stgArgs
     _ -> if tyArity > arity
      then StgInstr StgPAp (StgVarArg (convName' fId) : stgArgs)
      else StgApp (convName' fId) stgArgs

 -- TODO default case alt
 Case expr a -> case a of
   Switch alts ->
    let convAlt (c, e) = (literal2Stg c, convExpr' e)
    in StgCase (convExpr' expr) Nothing (StgSwitch$convAlt <$> alts)
   Decon  alts   -> -- [(IName, [IName], CoreExpr)]
    let convAlt (con, arg, e)
              = (convName' con, convName' <$> arg, convExpr' e)
    in StgCase (convExpr' expr) Nothing (StgDeconAlts$convAlt<$>alts)

 TypeExpr t -> error "internal error: core2Stg: unexpected typeExpr"
 WildCard   -> error "found hole"

-- cancerous llvm-hs Name policy
-- TODO name clashes ?
-- core inames are unique, but llvm will complain that they are
-- not given sequentially (since they don't all end up in stg)
-- prepending a '_' to force a string name is not ideal
convName :: IName -> Maybe HName -> StgId
convName i = \case
  Nothing -> LLVM.AST.mkName $ '_' : show i
--Nothing -> LLVM.AST.UnName $ fromIntegral i
  Just h  -> LLVM.AST.mkName $ CU.hNm2Str h -- ++ show i

typedLit2Stg :: Literal -> Type -> StgConst = \l t ->
  let mkChar c = C.Int 8 $ toInteger $ ord c 
      unEither f = fst . either error id . f
  in case t of
  TyMono (MonoTyPrim p) -> case p of
    PrimInt bits  -> let ti = case l of { PolyInt i -> i }
      in C.Int (fromIntegral bits) $ unEither TR.decimal ti
    PrimFloat fTy -> let tf = case l of { PolyInt t->t ; PolyFrac t->t}
      in case fTy of
      FloatTy  -> C.Float (LF.Single $ unEither TR.rational tf)
      DoubleTy -> C.Float (LF.Double $ unEither TR.rational tf) -- fromRational
    PrimArr ty -> let String s = l in
      C.Array (LLVM.AST.IntegerType 8) (mkChar <$> (s++['\0']))
    x -> literal2Stg l -- no overrides fancy
  TyInstance t2 _ -> typedLit2Stg l t2
  o -> literal2Stg l
--o -> error $ "bad type for literal: " ++ show l ++ " : " ++ show o

literal2Stg :: Literal -> StgConst = \l ->
  let mkChar c = C.Int 8 $ toInteger $ ord c 
  in case l of
    Char c   -> mkChar c
    String s -> C.Array (LLVM.AST.IntegerType 8) (mkChar<$>(s++['\0']))
--    Int i    -> C.Int 32 $ i
--    Frac f   -> C.Float (LF.Double $ fromRational f)

-- most llvm instructions take flags, stg wants functions on operands
prim2llvm :: PrimInstr -> StgPrimitive = \case
  IntInstr i  -> StgPrim2 $ case i of
      Add  -> \a b -> L.Add False False a b []
      Sub  -> \a b -> L.Sub False False a b []
      Mul  -> \a b -> L.Mul False False a b []
      SDiv -> \a b -> L.SDiv False      a b []
      SRem -> \a b -> L.SRem            a b []
      ICmp -> \a b -> L.ICmp IP.EQ      a b []
      And  -> \a b -> L.And             a b []
      Or   -> \a b -> L.Or              a b []
      Xor  -> \a b -> L.Xor             a b []
      Shl  -> \a b -> L.Shl False False a b []
      Shr  -> \a b -> L.LShr False      a b []
  NatInstr i  -> StgPrim2 $ case i of
      UDiv -> \a b -> L.UDiv False a b []
      URem -> \a b -> L.URem a b []
  FracInstr i -> StgPrim2 $ case i of
      FAdd -> \a b -> L.FAdd L.noFastMathFlags a b []
      FSub -> \a b -> L.FSub L.noFastMathFlags a b []
      FMul -> \a b -> L.FMul L.noFastMathFlags a b []
      FDiv -> \a b -> L.FDiv L.noFastMathFlags a b []
      FRem -> \a b -> L.FRem L.noFastMathFlags a b []
      FCmp -> \a b -> L.FCmp FP.UEQ a b []
  MemInstr i -> case i of
      Gep        -> StgGep
      ExtractVal -> StgExtractVal -- idx
      InsertVal  -> StgInsertVal
  -- StgPrim1 $ \a -> L.ExtractValue a [fromIntegral idx] []
  -- InsertVal  -> \a b -> L.InsertValue True a [b] []
  MkTuple -> StgMkTuple
  Alloc   -> StgAlloc
  t -> error $ show t

primTy2llvm :: PrimType -> LLVM.AST.Type =
  let doExtern isVa tys =
        let (argTys, [retTy]) = splitAt (length tys -1) tys
        in LT.FunctionType retTy argTys isVa
  in \case
  PrimInt   i   -> LT.IntegerType $ fromIntegral i
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
