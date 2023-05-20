module CoreUtils where
----------------------------------------------------
-- Various utility functions operating on CoreSyn --
----------------------------------------------------
-- Any function that could be given in CoreSyn directly is found here
import CoreSyn
import ShowCore()
import PrettyCore
import Prim
import qualified BitSetMap as BSM
import Data.List (union , intersect)

makeLabel q = let sumTy = THSumTy (BSM.singleton (qName2Key q) (TyGround [THTyCon $ THTuple mempty]))
  in Core (Label q []) (TyGround [THTyCon sumTy])

mkLiteralEquality :: Literal -> Term -> Term
mkLiteralEquality l x = case l of
  Char _ -> App (Instr $ NumInstr (PredInstr EQCmp)) [Lit l , x]
  I32  _ -> App (Instr $ NumInstr (PredInstr EQCmp)) [Lit l , x]
  l -> Poison $ "todo literal equality on " <> show l

getArgShape :: Term -> ArgShape
getArgShape = \case
  Label l params -> ShapeLabel l (getArgShape <$> params)
  Var (VQBind q) -> ShapeQBind q
  _ -> ShapeNone

isPoisonExpr :: Expr -> Bool = (\case { Core (Poison{}) _ -> True ; _ -> False })

mapTHeads fn = \case
  TyVarsF vs g -> TyVarsF vs (fn <$> g)
  TyGroundF g  -> TyGroundF  (fn <$> g)
  x -> x

tyVars vs g = if vs == 0 then TyGround g else TyVars vs g
hasTVars = \case { TyVars{} -> True ; _ -> False }

partitionType :: Type -> (BitSet , GroundType)
partitionType = \case
  TyVars vs g -> (vs , g)
  TyGround g  -> (0  , g)
  TySet n     -> (0 , [])
--TyVar v     -> (0 `setBit` v , [])
--pi@TyPi{}   -> (0 , [pi]) -- TODO ok?
--TyIndexed{} -> _
  t -> error $ show t

tyLatticeEmpty pos = \case
  TyGround [] -> TyGround [if pos then THBot else THTop] -- pure ty
  t  -> t

hasVar t v = case t of
  TyVars vs _ -> testBit vs v
  _ -> False

--mkTHArrow :: [[TyHead]] -> [TyHead] -> Type
mkTyArrow args retTy = [THTyCon $ THArrow args retTy]

getArrowArgs = \case
  TyGround [THTyCon (THArrow as r)] -> (as , r)
  TyGround [THBi _ t] -> getArrowArgs t
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
  [THBi i (TyGround t)] -> [THBi i $ TyGround $ prependArrowArgs args t]
  x -> [THTyCon $ THArrow (TyGround <$> args) (TyGround x)]

prependArrowArgsTy :: [Type] -> Type -> Type
prependArrowArgsTy [] = identity
prependArrowArgsTy args = \case
  TyGround [THTyCon (THArrow as r)] -> TyGround [THTyCon $ THArrow (args ++ as) r]
  TyGround [THBi i t] -> TyGround [THBi i $ prependArrowArgsTy args t]
  x -> TyGround [THTyCon $ THArrow args x]

isTyCon = \case
 THTyCon{} -> True
 _         -> False

-- expr2Ty :: _ -> Expr -> TCEnv s Type
-- Expression is a type (eg. untyped lambda calculus is both a valid term and type)
expr2Ty e = case e of
 Core (Ty x) (TySet _n) -> pure x
 x -> error $ "raw term cannot be a type: " ++ show x

bind2Expr = naiveExpr

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
    THSumOpen{} -> KSum
    THTuple{}   -> KTuple
  THBound{} -> KBound
  THMuBound{} -> KRec
  THMu{}      -> KRec
  _ -> KAny

intersectTypes :: Type -> Type -> Type
intersectTypes a b = case (partitionType a , partitionType b) of
  ((v , g) , (w , f)) -> TyVars (v .&. w) (intersect f g)

unionTypes :: Type -> Type -> Type
unionTypes a b = case (partitionType a , partitionType b) of
  ((v , g) , (w , f)) -> TyVars (v .|. w) (union f g)

mergeTyUnions :: Bool -> [TyHead] -> [TyHead] -> [TyHead]
mergeTyUnions pos l1 l2 = let
  cmp a b = case (a,b) of
    (THBound a' , THBound b') -> compare a' b'
    (THMu m _ , THMuBound n) -> compare m n
    (THMuBound n , THMu m _) -> compare m n
    _ -> kindOf a `compare` kindOf b
  in foldr (mergeTyHeadType pos) [] (sortBy cmp $ l2 ++ l1)

mergeTyHeadType :: Bool -> TyHead -> [TyHead] -> [TyHead]
mergeTyHeadType pos newTy = \case
  []       -> [newTy]
  ty : tys -> mergeTyHead pos newTy ty ++ tys

mergeTyHead :: Bool -> TyHead -> TyHead -> [TyHead]
mergeTyHead pos t1 t2 = -- (\ret -> trace (prettyTyRaw (TyGround [t1]) <> " ~~ " <> prettyTyRaw (TyGround [t2]) <> " => " <> prettyTyRaw (TyGround ret)) ret) $
  let join = [t1 , t2]
      zM  :: Semialign f ⇒ Bool -> f Type -> f Type -> f Type
      zM pos' = alignWith (these identity identity (mergeTypes pos'))
      mT = mergeTypes pos
  in case join of
  [THTop , THTop] -> [THTop]
  [THBot , THBot] -> [THBot]
  [THPrim a , THPrim b]  -> if a == b then [t1] else case (a,b) of
--  (PrimInt x , PrimInt y) -> [THPrim $ PrimInt $ max x y]
    (PrimBigInt , PrimInt _) -> [THPrim $ PrimBigInt]
    (PrimInt _ , PrimBigInt) -> [THPrim $ PrimBigInt]
    _ -> join

  -- v should avoid producing this
  [THMu m _ , THMuBound n] -> if m == n then [t1] else join
  [THMuBound n , THMu m _] -> if m == n then [t2] else join

  [THMu m _ , THBound n]  -> if m == n then [t1] else join
  [THBound n , THMu m _]  -> if m == n then [t2] else join
  [THMu m mt , THMu n nt] -> if m == n then [THMu m (mergeTypes pos mt nt)] else join
  [THBi m mt , THBi n nt] -> if m == n then [THBi m (mergeTypes pos mt nt)] else join -- TODO slightly dodgy
  [THMuBound a , THMuBound b] -> if a == b then [t1] else join
  [THMu m a , b] -> [THMu m (mergeTypes pos a (TyGround [b]))]
  [a , THMu m b] -> [THMu m (mergeTypes pos (TyGround [a]) b)]

  [THBound a , THBound b]     -> if a == b then [t1] else join
  [THExt a , THExt  b]        -> if a == b then [t1] else join
  [THTyCon t1 , THTyCon t2]   -> case [t1,t2] of
--  [THSumTy a   , THSumTy b]   -> [THTyCon $ THSumTy   $ if pos then BSM.intersectionWith mT a b else BSM.unionWith mT a b]
    [THSumTy a   , THSumTy b]   -> [THTyCon $ THSumTy   $ BSM.unionWith mT a b]
    [THProduct a , THProduct b] -> [THTyCon $ THProduct $ if pos then BSM.unionWith mT a b else BSM.intersectionWith mT a b]
    [THTuple a , THTuple b]     -> [THTyCon $ THTuple (zM pos a b)]
    [THArrow d1 r1 , THArrow d2 r2] | length d1 == length d2 -> [THTyCon $ THArrow (zM (not pos) d1 d2) (mergeTypes pos r1 r2)]
    _ -> join
  _ -> join

getTyVars = \case
  TyVars vs _ -> vs
  _ -> 0

nullType = \case
  TyVars 0 [] -> True
  TyGround [] -> True
  _ -> False

mergeTypeList :: Bool -> [Type] -> Type
mergeTypeList pos ts = let r = foldr (mergeTypes pos) (TyGround []) ts
  in r -- trace (T.intercalate " , " (prettyTyRaw <$> ts) <> " ⇒ " <> prettyTyRaw r) r

rmMuBound m = let goGround = filter (\case { THMuBound x -> x /= m ; _ -> True }) in \case
  TyGround g  -> TyGround (goGround g)
  TyVars vs g -> TyVars vs (goGround g)
  t -> t

rmTVar v = \case
  TyVars ws g -> TyVars (ws `clearBit` v) g
  t -> t

mergeTVars vs = \case
  TyVars ws g -> TyVars (ws .|. vs) g
  TyGround g  -> TyVars vs g
mergeTypeGroundType pos a b = mergeTypes pos a (TyGround b)
mergeTVar v = \case
  TyVars ws g -> TyVars (ws `setBit` v) g
  TyGround g  -> TyVars (0  `setBit` v) g
  TySet n     -> tyVar v -- TODO ?!
mergeTypes pos a b = {-d_ (a , b) $-} mergeTypes' pos a b
mergeTypes' pos (TyGround a) (TyGround b)     = TyGround (mergeTyUnions pos a b)
mergeTypes' pos (TyVars vs g1) (TyVars ws g2) = TyVars (vs .|. ws) (mergeTyUnions pos g1 g2)
mergeTypes' pos (TyVars vs g1) (TyGround g2)  = TyVars vs (mergeTyUnions pos g1 g2)
mergeTypes' pos (TyGround g1) (TyVars vs g2)  = TyVars vs (mergeTyUnions pos g1 g2)
mergeTypes' pos a b = error $ "attempt to merge weird types at " <> if pos then "+" else "-" <> ": " <> show (a , b)

-- TODO check at the same time if this did anything
mergeTysNoop :: Bool -> Type -> Type -> Maybe Type = \pos a b -> Just $ mergeTypes pos a b
