-- core2Stg
-- * all LBinds must have a type annotation
-- * all types must be monotypes
-- * this function should never fail
--
-- ? how to make dependent types static by this point ?
-- ? also type functions etc..
module Core2Stg (core2stg)
where

import CoreSyn
import StgSyn

import qualified CoreUtils as CU
import qualified Data.Vector as V
import qualified LLVM.AST (Operand, Instruction, Type, Name, mkName)
import qualified LLVM.AST.Constant (Constant)

core2stg :: CoreModule -> StgModule
core2stg (CoreModule algData coreBinds defaults tyFuns)
 = StgModule stgData stgTypedefs stgBinds
  where
  (stgData, stgTypedefs) = convData algData
  stgBinds = doBinds coreBinds algData

-- handle the algData TypeMap (NameMap Entity)
-- This should only contain TyAlias and MonoTyDatas
convData :: TypeMap -> (V.Vector StgData, V.Vector (StgId, StgType))
convData tyMap = (stgData, aliases)
 where convTy' = convTy tyMap
       aliases = V.empty
       -- the TypeMap only contains aliases and data
       stgTypes = convTy' . typed <$> tyMap
       stgData' = V.filter (\case { StgAlgType{}->True ; _ -> False }) stgTypes
       stgData = (\(StgAlgType d) -> d) <$> stgData'

-- needs the TypeMap in order to deref types
convTy :: TypeMap -> Type -> StgType
convTy tyMap =
  let deref = (tyMap V.!)
      convTy' = convTy tyMap
  in \case
  TyAlias iNm -> StgTypeAlias $ convName iNm (named $ deref iNm)
  TyArrow types -> StgFnType (convTy' <$> types)
  TyMono m -> case m of
      MonoTyLlvm llvmty -> StgLlvmType llvmty
      MonoTyData dataName types -> StgAlgType $ mkStgData types
          where
          -- an StgData is a sumtype of product types
          -- TODO how to get the names ? for constructors and the data itself
          getName hNm = LLVM.AST.mkName $ CU.hNm2Str hNm
          mkStgData :: [(HName, Type)] -> StgData
          mkStgData tys = 
            let mkAlt (nm, TyArrow tys) =
                  StgProductType (getName nm) $ convTy' <$> tys
            in StgSumType (getName dataName) $ mkAlt <$> tys

  -- Note any other type is illegal at this point
  t -> error ("internal error: core2Stg: note a monotype: " ++ show t)

-- the V.imap will give us the right inames since all terms are in the bindMap
doBinds :: V.Vector Binding -> TypeMap -> V.Vector StgBinding
doBinds binds tyMap = V.fromList $ V.ifoldr f [] binds
  where
  convTy' = convTy tyMap
  lookupBind i = CU.lookupBinding i binds
  convName' i = convName i $ named $ info $ lookupBind i
  f iNm = \case
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
 Var nm               -> StgLit $ StgVarArg $ convName' nm
 Lit lit              -> case lit of
     ExternFn l -> _ 
     LlvmLit l -> StgLit $ StgConstArg l
 Instr prim args      -> _
 App (Var fId) args   -> StgApp (convName' fId)
                                (StgExprArg . convExpr' <$> args)

 -- TODO default case alt
 SwitchCase expr alts ->
    let convAlt (LlvmLit c, e) = (c, convExpr' e)
        convAlt f = error ("unexpected extern function: " ++ show f)
    in StgCaseSwitch (convExpr' expr) Nothing (convAlt <$> alts)
 DataCase expr alts   -> -- [(IName, [IName], CoreExpr)]
    let convAlt (con, arg, e)
              = (convName' con, convName' <$> arg, convExpr' e)
    in StgDataCase (convExpr' expr) Nothing (convAlt<$>alts)

 TypeExpr t           -> error "internal error: core2Stg: unexpected typeExpr"
 WildCard             -> _ -- means this binding should error if evaluated

-- cancerous llvm-hs Name policy
-- TODO name clashes ?
convName :: IName -> Maybe HName -> StgId
convName i = \case
  Nothing -> LLVM.AST.mkName $ show i
  Just h  -> LLVM.AST.mkName $ CU.hNm2Str h -- ++ show i
