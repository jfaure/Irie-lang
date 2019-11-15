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
import qualified Data.Vector as V
import qualified LLVM.AST as L -- (Operand, Instruction, Type, Name, mkName)
import qualified LLVM.AST  -- (Operand, Instruction, Type, Name, mkName)
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.FloatingPointPredicate as FP
import qualified LLVM.AST.Type as LT
import qualified LLVM.AST.Float as LF
import           LLVM.AST.AddrSpace
import Data.List

-- TODO filter all functions from CoreModule.bindings
core2stg :: CoreModule -> StgModule
core2stg (CoreModule algData coreBinds externs overloads defaults)
 = StgModule stgData (V.fromList stgTypedefs) stgExterns stgBinds
  where
  (stgData, stgTypedefs) = convData algData
  stgBinds               = doBinds coreBinds algData
  stgExterns             = V.imap (doExtern algData) externs

doExtern :: TypeMap -> IName -> Entity -> StgBinding
doExtern tyMap iNm (Entity (Just nm) ty) =
  let llvmFnTy   = (\(StgLlvmType t) -> t) $ convTy tyMap ty
      stgId      = convName iNm (Just nm)
  in StgBinding stgId (StgExt llvmFnTy)

-- handle the algData TypeMap (NameMap Entity)
-- This returns the TyAliases monotyDatas
convData :: TypeMap -> (V.Vector StgData, [(StgId, StgType)])
convData tyMap = mkLists $ foldr f ([],[]) tyMap
  where
  mkLists (a,b) = (V.fromList a, b)
  f (Entity (Just hNm) (TyMono (MonoRigid r))) (d, a) = (d,a)
  f (Entity (Just hNm) (TyPoly (PolyData ty dataDef))) (datas, aliases)
    = let (newData, subTys) = convDataDef tyMap dataDef
      in  (newData : datas, subTys ++ aliases)
  f (Entity _       TyPoly{}) acc = acc -- don't conv polytypes
  f (Entity (Just hNm) rawTy) (datas, aliases) =
      let ty = convTy tyMap rawTy
          nm = LLVM.AST.mkName (CU.hNm2Str hNm)
      in  (datas, (nm, ty):aliases)

convDataDef :: TypeMap -> DataDef -> (StgData, [(StgId, StgType)])
convDataDef tyMap (DataDef dataNm sumAlts) =
  let deref = (tyMap V.!)
      mkStgId = LLVM.AST.mkName . CU.hNm2Str
      mkProdData (pNm, tys)
        = StgProductType (mkStgId pNm) $ convTy tyMap <$> tys
      sumTy = StgSumType (mkStgId dataNm) $ mkProdData <$> sumAlts
      qual = dataNm `T.snoc` '.'
      subAliases = (\(pNm, tys) -> mkStgId $ qual `T.append` pNm) <$> sumAlts
  in  (sumTy, zip subAliases (repeat $ StgTypeAlias $ mkStgId dataNm))

-- needs the TypeMap in order to deref types
convTy :: TypeMap -> Type -> StgType
convTy tyMap =
  let deref = (tyMap V.!)
      convTy' = convTy tyMap
      mkAlias iNm = convName iNm (named $ deref iNm)
  in \case
  TyAlias iNm         -> StgTypeAlias $ mkAlias iNm
  TyArrow types       -> StgFnType (convTy' <$> types)
  TyMono m            -> case m of
    MonoTyPrim prim -> StgLlvmType  $ primTy2llvm prim
    MonoRigid  riNm -> StgTypeAlias $ mkAlias riNm

  TyExpr tyfun -> error ("dependent type: " ++ show tyfun)

  -- Note any other type is illegal at this point
  t -> error ("internal error: core2Stg: not a monotype: " ++ show t)

-- the V.imap will give us the right inames since all terms are in the bindMap
doBinds :: V.Vector Binding -> TypeMap -> V.Vector StgBinding
doBinds binds tyMap = V.fromList $ V.ifoldr f [] binds
  where
  convTy'      = convTy tyMap
  lookupBind i = CU.lookupBinding i binds
  convName' i  = convName i $ named $ info $ lookupBind i
  f iNm        = \case
    LBind _ (Instr i) _  -> id -- don't try to gen primitives
    LBind args expr info ->
      let nm       = convName iNm (named info)
          argNames = StgVarArg . convName' <$> args
          (argTys, [retTy]) = case args of
              [] -> ([], [convTy' $ typed info])
              t  -> case typed info of
                  TyArrow tys -> splitAt (length tys - 1) $ convTy' <$> tys
                  _ -> error "internal typecheck error"
          stgExpr = convExpr binds expr
      in (StgBinding nm (StgRhsClosure argNames argTys retTy stgExpr) :)
    _ -> id

convExpr :: BindMap -> CoreExpr -> StgExpr
convExpr bindMap =
  let lookup      = (bindMap V.!)
      convExpr'   = convExpr bindMap
      convName' i = convName i $ named $ info $ lookup i
      typeOf      = typed . info . lookup
 in \case
 Var nm                -> StgLit $ StgVarArg $ convName' nm
 Lit lit               -> StgLit $ StgConstArg $ literal2Stg lit
 App fn args           -> case fn of
    (Var fId)    ->
      let bind = lookup fId
          instanciate = case bind of
            b@(LClass i) -> traceShow i b
            b            -> b
      in  StgApp (convName' fId) (StgExprArg . convExpr' <$> traceShow instanciate args)
 
    (Instr prim) -> case (convExpr' <$> args) of
        [a, b] -> StgPrimOp $ StgPrimBinOp (prim2llvm prim) a b
        _      -> error "unsupported arity for primInstr"
 
    weirdFn -> error ("panic: core2Stg: not a function: " ++ show weirdFn)

 -- TODO default case alt
 SwitchCase expr alts ->
    let convAlt (c, e) = (literal2Stg c, convExpr' e)
    in StgCaseSwitch (convExpr' expr) Nothing (convAlt <$> alts)
 DataCase expr alts   -> -- [(IName, [IName], CoreExpr)]
    let convAlt (con, arg, e)
              = (convName' con, convName' <$> arg, convExpr' e)
    in StgDataCase (convExpr' expr) Nothing (convAlt<$>alts)

 TypeExpr t -> error "internal error: core2Stg: unexpected typeExpr"
 WildCard   -> error "found hole"
 Instr i -> error ("core2Stg: unsaturated primInstr" ++ show i)

-- cancerous llvm-hs Name policy
-- TODO name clashes ?
convName :: IName -> Maybe HName -> StgId
convName i = \case
  Nothing -> LLVM.AST.UnName $ fromIntegral i
  Just h  -> LLVM.AST.mkName $ CU.hNm2Str h -- ++ show i

-- TODO depends on the type of the Literal ?!
literal2Stg :: Literal -> StgConst =
  let mkChar c = C.Int 8 $ toInteger $ ord c 
  in \case
    Char c   -> mkChar c
    Int i    -> C.Int 32 $ i
    String s -> C.Array (LLVM.AST.IntegerType 8) (mkChar <$> s)
    Frac f   -> C.Float (LF.Double $ fromRational f)

-- most llvm instructions take flags, stg wants functions on operands
prim2llvm :: PrimInstr -> StgBinOp
 = \case
  IntInstr i  -> case i of
      Add  -> \a b -> L.Add False False a b []
      Sub  -> \a b -> L.Sub False False a b []
      Mul  -> \a b -> L.Mul False False a b []
      SDiv -> \a b -> L.SDiv False a b []
      SRem -> \a b -> L.SRem a b []
      ICmp -> \a b -> L.ICmp IP.EQ a b []
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
  MemInstr i -> case i of
  {}
   -- ExtractVal -> \a b -> L.ExtractValue a b
   -- InsertVal  -> \a b -> L.InsertValue  a b
   -- Gep        -> \a b -> L.GetElementPtr True a b []

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

-- APInts etc.. should perhaps be as Functor module (ie. in prelude)
-- APInt   -> _
-- APFloat -> _
