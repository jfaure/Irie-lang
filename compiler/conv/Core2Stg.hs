-- core2Stg
-- * all LBinds must have a type annotation
-- * all types must be monotypes
-- * this function should never fail
--
-- ? how to make dependent types static by this point ?
-- ? also type functions etc..
module Core2Stg (core2stg)
where

import Prim
import CoreSyn
import StgSyn

import Data.Foldable (foldrM)
import Data.Char (ord)
import qualified CoreUtils as CU
import qualified Data.Vector as V
import qualified LLVM.AST as L -- (Operand, Instruction, Type, Name, mkName)
import qualified LLVM.AST  -- (Operand, Instruction, Type, Name, mkName)
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.IntegerPredicate as IP
import qualified LLVM.AST.FloatingPointPredicate as FP
import qualified LLVM.AST.Type as LT
import qualified LLVM.AST.Float as LF
import LLVM.AST.AddrSpace

-- TODO filter all functions from CoreModule.bindings
core2stg :: CoreModule -> StgModule
core2stg (CoreModule algData coreBinds classFns defaults)
 = StgModule stgData stgTypedefs stgBinds
  where
  (stgData, stgTypedefs) = convData algData
  stgBinds = doBinds coreBinds algData

-- handle the algData TypeMap (NameMap Entity)
-- This returns the TyAliases monotyDatas
convData :: TypeMap -> (V.Vector StgData, V.Vector (StgId, StgType))
convData tyMap = mkLists $ foldr f ([],[]) tyMap
  where
  mkLists (a,b) = (V.fromList a, V.fromList b)
  f (Entity (Just hNm) rawTy) (datas, aliases) = case convTy tyMap rawTy of
      StgAlgType d -> (d:datas, aliases)
      a            -> let nm = LLVM.AST.mkName (CU.hNm2Str hNm)
                      in (datas, (nm, a):aliases)
    

-- needs the TypeMap in order to deref types
convTy :: TypeMap -> Type -> StgType
convTy tyMap =
  let deref = (tyMap V.!)
      convTy' = convTy tyMap
  in \case
  TyAlias iNm -> StgTypeAlias $ convName iNm (named $ deref iNm)
  TyArrow types -> StgFnType (convTy' <$> types)
  TyMono m -> case m of
      MonoTyPrim prim -> StgLlvmType $ primTy2llvm prim

      -- MonoTyData HName [(HName, [Type])]
      MonoTyData dataNm sumAlts ->
        let mkStgId nm = LLVM.AST.mkName $ CU.hNm2Str nm
            mkProdData (pNm, tys)
              = StgProductType (mkStgId pNm) $ convTy' <$> tys
            sumData = StgSumType (mkStgId dataNm) $ mkProdData <$> sumAlts
        in  StgAlgType sumData

  -- Note any other type is illegal at this point
  t -> error ("internal error: core2Stg: not a monotype: " ++ show t)

-- the V.imap will give us the right inames since all terms are in the bindMap
doBinds :: V.Vector Binding -> TypeMap -> V.Vector StgBinding
doBinds binds tyMap = V.fromList $ V.ifoldr f [] binds
  where
  convTy' = convTy tyMap
  lookupBind i = CU.lookupBinding i binds
  convName' i = convName i $ named $ info $ lookupBind i
  f iNm = \case
    LBind _ (Instr i) _  -> id -- don't try to gen primitives
    LBind args expr info ->
      let nm = convName iNm (named info)
          argNames = StgVarArg . convName' <$> args
          (argTys, [retTy]) = case args of
              [] -> ([], [convTy' $ typed info])
              t -> case typed info of
                  TyArrow tys -> splitAt (length tys - 1) $ convTy' <$> tys
                  _ -> error "internal typecheck error"
          stgExpr = convExpr binds expr
      in (StgBinding nm (StgRhsClosure argNames argTys retTy stgExpr) :)
    _ -> id

convExpr :: BindMap -> CoreExpr -> StgExpr
convExpr bindMap =
 let lookup = (bindMap V.!)
     convExpr' = convExpr bindMap
     convName' i = convName i $ named $ info $ lookup i
 in \case
 Var nm                -> StgLit $ StgVarArg $ convName' nm
 Lit lit               -> StgLit $ StgConstArg $ literal2Stg lit
 App fn args           -> case fn of
   (Var fId)    -> StgApp (convName' fId) (StgExprArg . convExpr' <$> args)
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

 TypeExpr t           -> error "internal error: core2Stg: unexpected typeExpr"
 WildCard             -> _ -- means this binding should error if evaluated
 Instr i -> error ("core2Stg: unsaturated primInstr" ++ show i)

-- cancerous llvm-hs Name policy
-- TODO name clashes ?
convName :: IName -> Maybe HName -> StgId
convName i = \case
  Nothing -> LLVM.AST.mkName $ show i
  Just h  -> LLVM.AST.mkName $ CU.hNm2Str h -- ++ show i

-- TODO depends on the type of the Literal ?!
literal2Stg :: Literal -> StgConst =
  let mkChar c = C.Int 8 $ toInteger $ ord c 
  in \case
    Char c   -> mkChar c
    Int i    -> C.Int 32 $ i
    String s -> C.Array (LLVM.AST.IntegerType 8) (mkChar <$> s)
    Frac f   -> C.Float (LF.Double $ fromRational f)

prim2llvm :: PrimInstr -> StgBinOp
 = \case
  IntInstr i -> case i of
      Add -> \a b  -> L.Add False False a b []
      Sub -> \a b  -> L.Sub False False a b []
      Mul -> \a b  -> L.Mul False False a b []
      SDiv -> \a b -> L.SDiv False a b []
      SRem -> \a b -> L.SRem a b []
      ICmp -> \a b -> L.ICmp IP.EQ a b []
  NatInstr i -> case i of
      UDiv -> \a b -> L.UDiv False a b []
      URem -> \a b -> L.URem a b []
  FracInstr i -> case i of
      FAdd -> \a b  -> L.FAdd L.noFastMathFlags a b []
      FSub -> \a b  -> L.FSub L.noFastMathFlags a b []
      FMul -> \a b  -> L.FMul L.noFastMathFlags a b []
      FDiv -> \a b  -> L.FDiv L.noFastMathFlags a b []
      FRem -> \a b  -> L.FRem L.noFastMathFlags a b []
      FCmp -> \a b  -> L.FCmp FP.UEQ a b []
  MemInstr i -> case i of
  {}
   -- ExtractVal -> \a b -> L.ExtractValue a b
   -- InsertVal  -> \a b -> L.InsertValue  a b
   -- Gep        -> \a b -> L.GetElementPtr True a b []

primTy2llvm :: PrimType -> LLVM.AST.Type
 = \case
  PrimInt   i   -> LT.IntegerType $ fromIntegral i
  PrimFloat f   -> LT.FloatingPointType $ case f of
      HalfTy    -> LT.HalfFP
      FloatTy   -> LT.FloatFP
      DoubleTy  -> LT.DoubleFP
      FP128     -> LT.FP128FP
      PPC_FP128 -> LT.PPC_FP128FP
  PtrTo ty -> LT.PointerType (primTy2llvm ty) (AddrSpace 0)
-- Extern   tys -> 
-- ExternVA tys ->

-- APInts etc.. should perhaps be as Functor module (ie. in prelude)
-- APInt   -> _
-- APFloat -> _

