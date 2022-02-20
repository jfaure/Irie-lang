module CoreUtils where
----------------------------------------------------
-- Various utility functions operating on CoreSyn --
----------------------------------------------------
-- Any function that could be given in CoreSyn directly is found here
import CoreSyn
import ShowCore()
import PrettyCore
import Prim
import qualified Data.IntMap as IM
import qualified Data.Vector as V

-- eqTypes a b = all identity (zipWith eqTyHeads a b) -- not zipwith !
eqTypes (TyGround a) (TyGround b) = all identity (alignWith (these (const False) (const False) eqTyHeads) a b)

eqTyHeads a b = kindOf a == kindOf b && case (a,b) of
  (THPrim a  , THPrim b)  -> a == b
  (THTyCon a , THTyCon b) -> case did_ (a,b) of
    (THSumTy a , THSumTy b) -> all identity $ IM.elems $ alignWith (these (const False) (const False) eqTypes) a b
    (THTuple a , THTuple b) -> all identity $ V.zipWith eqTypes a b
  _ -> False

partitionType = \case
  TyVars vs g -> (vs , g)
  TyGround g  -> (0  , g)
  TyVar v     -> (0 `setBit` v , [])

tyLatticeEmpty pos = \case
  TyGround [] -> TyGround [if pos then THBot else THTop] -- pure ty
  t  -> t

hasVar t v = case t of
  TyGround{}  -> False
  TyVar w     -> v == w
  TyVars vs g -> testBit vs v

--mkTHArrow :: [[TyHead]] -> [TyHead] -> Type
mkTyArrow args retTy = [THTyCon $ THArrow args retTy]

getArrowArgs = \case
  TyGround [THTyCon (THArrow as r)] -> (as , r)
  TyGround [THBi i m t] -> getArrowArgs t
  t -> trace ("not a function type: " <> prettyTyRaw t) ([] , t)

-- appendArrowArgs [] = identity
-- appendArrowArgs args = \case
--   [THTyCon (THArrow as r)] -> [THTyCon $ THArrow (as ++ args) r]
--   [THPi (Pi p t)]   -> [THPi (Pi p $ appendArrowArgs args t)]
--   [THSi (Pi p t) _] -> [THPi (Pi p $ appendArrowArgs args t)]
--   [THBi i t] -> [THBi i $ appendArrowArgs args t]
--   x -> [THTyCon $ THArrow args x]

prependArrowArgs :: [[TyHead]] -> [TyHead] -> [TyHead]
prependArrowArgs [] = identity
prependArrowArgs args = \case
  [THTyCon (THArrow as r)] -> [THTyCon $ THArrow ((TyGround <$> args) ++ as) r]
  [THBi i m (TyGround t)] -> [THBi i m $ TyGround $ prependArrowArgs args t]
  x -> [THTyCon $ THArrow (TyGround <$> args) (TyGround x)]

prependArrowArgsTy :: [Type] -> Type -> Type
prependArrowArgsTy [] = identity
prependArrowArgsTy args = \case
  TyGround [THTyCon (THArrow as r)] -> TyGround [THTyCon $ THArrow (args ++ as) r]
  TyGround [THBi i m t] -> TyGround [THBi i m $ prependArrowArgsTy args t]
  x -> TyGround [THTyCon $ THArrow args x]

isTyCon = \case
 THTyCon{} -> True
 _         -> False

tyOfTy :: Type -> Type
tyOfTy t = TyGround [THSet 0]

tyExpr = \case -- expr found as type, (note. raw exprs cannot be types however)
  Ty t -> Just t
  expr -> Nothing --error $ "expected type, got: " ++ show expr

tyOfExpr  = \case
  Core x ty -> ty
  Ty t      -> tyOfTy t
  PoisonExpr-> TyGround []
  m@MFExpr{}-> error $ "unexpected mfexpr: " <> show m

-- expr2Ty :: _ -> Expr -> TCEnv s Type
-- Expression is a type (eg. untyped lambda calculus is both a valid term and type)
expr2Ty judgeBind e = case e of
 Ty x -> pure x
 Core c ty -> case c of
-- Var (VBind i) -> pure [THRecSi i []]
   Var (VArg x)  -> pure $ TyVar x --[THVar x] -- TODO ?!
-- App (Var (VBind fName)) args -> pure [THRecSi fName args]
   x -> error $ "raw term cannot be a type: " ++ show e
 PoisonExpr -> pure $ TyGround [THPoison]
 x -> error $ "raw term cannot be a type: " ++ show x

bind2Expr = \case
  BindOK e    -> e

------------------------
-- Type Manipulations --
------------------------
--eqTyHead a b = kindOf a == kindOf b
kindOf = \case
  THPrim p  -> KPrim p
  THTyCon t -> case t of
    THArrow{}   -> KArrow
    THProduct{} -> KProd
    THSumTy{}   -> KSum
    THTuple{}   -> KTuple
  THBound{} -> KBound
  THMuBound{} -> KRec
  _ -> KAny

mergeTyUnions :: [TyHead] -> [TyHead] -> [TyHead]
mergeTyUnions l1 l2 = let
  cmp a b = case (a,b) of
    (THBound a' , THBound b') -> compare a' b'
    _ -> (kindOf a) `compare` (kindOf b)
  in foldr mergeTyHeadType [] (sortBy cmp $ l2 ++ l1)

(+:) = mergeTyHeadType

mergeTyHeadType :: TyHead -> [TyHead] -> [TyHead]
mergeTyHeadType newTy [] = [newTy]
mergeTyHeadType newTy (ty:tys) = mergeTyHead newTy ty ++ tys

mergeTyHead :: TyHead -> TyHead -> [TyHead]
mergeTyHead t1 t2 = -- trace (show t1 ++ " ~~ " ++ show t2) $
  let join = [t1 , t2]
      zM  :: Semialign f => f Type -> f Type -> f Type
      zM  = alignWith (these identity identity mergeTypes)
  in case join of
  [THTop , THTop] -> [THTop]
  [THBot , THBot] -> [THBot]
  [THSet a , THSet b] -> [THSet $ max a b]
  [THPrim a , THPrim b]  -> if a == b then [t1] else case (a,b) of
--  (PrimInt x , PrimInt y) -> [THPrim $ PrimInt $ max x y]
    (PrimBigInt , PrimInt y) -> [THPrim $ PrimBigInt]
    (PrimInt y , PrimBigInt) -> [THPrim $ PrimBigInt]
    _ -> join
  [THMuBound a , THMuBound b] -> if a == b then [t1] else join
  [THBound a , THBound b]     -> if a == b then [t1] else join
  [THExt a , THExt  b]        -> if a == b then [t1] else join
  [THTyCon t1 , THTyCon t2]   -> case [t1,t2] of -- TODO depends on polarity (!)
    [THSumTy a   , THSumTy b]   -> [THTyCon $ THSumTy   $ IM.unionWith mergeTypes a b]
    [THProduct a , THProduct b] -> [THTyCon $ THProduct $ IM.intersectionWith mergeTypes a b]
    [THTuple a , THTuple b]     -> [THTyCon $ THTuple   $ zM a b]
    [THArrow d1 r1 , THArrow d2 r2] | length d1 == length d2 -> [THTyCon $ THArrow (zM d1 d2) (mergeTypes r1 r2)]
    x -> join
  _ -> join

nullType = \case
  TyVars 0 [] -> True
  TyGround [] -> True
  _ -> False

mergeTypeList :: [Type] -> Type
mergeTypeList = foldr mergeTypes (TyGround [])

rmMuBound m = \case
  TyGround g -> TyGround $ filter (\case { THMuBound x -> x /= m ; _ -> True }) g
  t -> t

rmTVar v = \case
  TyVar w     -> if w == v then TyGround [] else TyVar w
  TyVars ws g -> TyVars (ws `clearBit` v) g
  TyGround g  -> TyGround g

mergeTVars vs = \case
  TyVar w     -> TyVars (vs `setBit` w) []
  TyVars ws g -> TyVars (ws .|. vs) g
  TyGround g  -> TyVars vs g
mergeTypeGroundType a b = mergeTypes a (TyGround b)
mergeTVar v = \case
  TyVar w     -> TyVars (setBit 0 w `setBit` v) []
  TyVars ws g -> TyVars (ws `setBit` v) g
  TyGround g  -> TyVars (0  `setBit` v) g
mergeTypes (TyGround a) (TyGround b)     = TyGround (mergeTyUnions a b)
mergeTypes (TyVar v) t                   = mergeTVar v t
mergeTypes t (TyVar v)                   = mergeTVar v t
mergeTypes (TyVars vs g1) (TyVars ws g2) = TyVars (vs .|. ws) (mergeTyUnions g1 g2)
mergeTypes (TyVars vs g1) (TyGround g2)  = TyVars vs (mergeTyUnions g1 g2)
mergeTypes (TyGround g1) (TyVars vs g2)  = TyVars vs (mergeTyUnions g1 g2)
mergeTypes a b = error $ "attempt to merge weird types: " <> show (a , b)
  
-- TODO check at the same time if this did anything
mergeTysNoop :: Type -> Type -> Maybe Type = \a b -> Just $ mergeTypes a b
