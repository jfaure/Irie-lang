module CoreUtils where
----------------------------------------------------
-- Various utility functions operating on CoreSyn --
----------------------------------------------------
-- Any function that could be given in CoreSyn directly is found here
import CoreSyn
import ShowCore()
import PrettyCore
import Prim
import Data.List (zipWith3 , partition)
import qualified Data.IntMap as IM
import qualified BitSetMap as BSM
import qualified Data.Vector as V

isPoisonExpr :: Expr -> Bool = (\case { PoisonExpr -> True ; _ -> False })

-- eqTypes a b = all identity (zipWith eqTyHeads a b) -- not zipwith !
eqTypes (TyGround a) (TyGround b) = all identity (alignWith (these (const False) (const False) eqTyHeads) a b)

eqTyHeads a b = kindOf a == kindOf b && case (a,b) of
  (THPrim a  , THPrim b)  -> a == b
  (THTyCon a , THTyCon b) -> case (a,b) of
    (THSumTy a , THSumTy b) -> all identity $ BSM.elems $ alignWith (these (const False) (const False) eqTypes) a b
    (THTuple a , THTuple b) -> all identity $ V.zipWith eqTypes a b
  _ -> False

partitionType = \case
  TyVars vs g -> (vs , g)
  TyGround g  -> (0  , g)
  TyVar v     -> (0 `setBit` v , [])
  t -> error $ show t

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
  TyGround [THBi i t] -> getArrowArgs t
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

tyOfTy :: Type -> Type
tyOfTy t = TyGround [THSet 0]

tyExpr = \case -- get the type from an expr.
  Ty t -> Just t
  Core e t -> Just (TyTerm e t)
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
  BindOK isRec e -> e

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

mergeTyUnions :: Bool -> [TyHead] -> [TyHead] -> [TyHead]
mergeTyUnions pos l1 l2 = let
  cmp a b = case (a,b) of
    (THBound a' , THBound b') -> compare a' b'
    _ -> (kindOf a) `compare` (kindOf b)
  in foldr (mergeTyHeadType pos) [] (sortBy cmp $ l2 ++ l1)

mergeTyHeadType :: Bool -> TyHead -> [TyHead] -> [TyHead]
mergeTyHeadType pos newTy [] = [newTy]
mergeTyHeadType pos newTy (ty:tys) = mergeTyHead pos newTy ty ++ tys

mergeTyHead :: Bool -> TyHead -> TyHead -> [TyHead]
mergeTyHead pos t1 t2 = -- trace (show t1 ++ " ~~ " ++ show t2) $
  let join = [t1 , t2]
      zM  :: Semialign f => Bool -> f Type -> f Type -> f Type
      zM pos' = alignWith (these identity identity (mergeTypes pos'))
      mT = mergeTypes pos
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
  [THTyCon t1 , THTyCon t2]   -> case [t1,t2] of
    [THSumTy a   , THSumTy b]   ->
      [THTyCon $ THSumTy $ if pos then BSM.unionWith mT a b else BSM.intersectionWith mT a b]
    [THProduct a , THProduct b] ->
      [THTyCon $ THProduct $ if pos then BSM.intersectionWith mT a b else BSM.unionWith mT a b]
    [THTuple a , THTuple b]     -> [THTyCon $ THTuple $ zM pos a b]
    [THArrow d1 r1 , THArrow d2 r2] | length d1 == length d2 -> [THTyCon $ THArrow (zM (not pos) d1 d2) (mergeTypes pos r1 r2)]
    x -> join
  _ -> join

nullType = \case
  TyVars 0 [] -> True
  TyGround [] -> True
  _ -> False

mergeTypeList :: Bool -> [Type] -> Type
mergeTypeList pos = foldr (mergeTypes pos) (TyGround [])

rmMuBound m = let goGround = filter (\case { THMuBound x -> x /= m ; _ -> True }) in \case
  TyGround g  -> TyGround (goGround g)
  TyVars vs g -> TyVars vs (goGround g)
  t -> t

rmTVar v = \case
  TyVar w     -> if w == v then TyGround [] else TyVar w
  TyVars ws g -> TyVars (ws `clearBit` v) g
  TyGround g  -> TyGround g

mergeTVars vs = \case
  TyVar w     -> TyVars (vs `setBit` w) []
  TyVars ws g -> TyVars (ws .|. vs) g
  TyGround g  -> TyVars vs g
mergeTypeGroundType pos a b = mergeTypes pos a (TyGround b)
mergeTVar v = \case
  TyVar w     -> TyVars (setBit 0 w `setBit` v) []
  TyVars ws g -> TyVars (ws `setBit` v) g
  TyGround g  -> TyVars (0  `setBit` v) g
mergeTypes pos (TyGround a) (TyGround b)     = TyGround (mergeTyUnions pos a b)
mergeTypes pos (TyVar v) t                   = mergeTVar v t
mergeTypes pos t (TyVar v)                   = mergeTVar v t
mergeTypes pos (TyVars vs g1) (TyVars ws g2) = TyVars (vs .|. ws) (mergeTyUnions pos g1 g2)
mergeTypes pos (TyVars vs g1) (TyGround g2)  = TyVars vs (mergeTyUnions pos g1 g2)
mergeTypes pos (TyGround g1) (TyVars vs g2)  = TyVars vs (mergeTyUnions pos g1 g2)
mergeTypes pos a b = error $ "attempt to merge weird types: " <> show (a , b)

-- TODO check at the same time if this did anything
mergeTysNoop :: Bool -> Type -> Type -> Maybe Type = \pos a b -> Just $ mergeTypes pos a b

-- Test if µ wrappers are unrollings of the recursive type `see eg. mapFold f l = foldr (\x xs => Cons (f x) xs) Nil l`
--    [Cons : {A , µC.[Cons : {A , µC} | Nil : {}]} | Nil : {}]
-- => µC.[Cons : {A , µC} | Nil : {}]
-- To do this pre-process the µ by 'inverting' it so we can incrementally test layers
-- This 'is' a zipper; like the cursor in a text editor or the pwd in a file system
data InvMu
  = Leaf IName
  | InvMu
  { this      :: Type -- A subtree of the µ. test eq ignoring the rec branch we came from
  , recBranch :: Int
  , parent    :: InvMu -- Nothing if root, Int is the parents tycon rec branch we're in
  } deriving Show

-- i is the wrapping tycon branch we recursed into to get here
-- ie. it should be ignored when testing if the parent layer is an unrolling of this µ
-- [InvMu]: one for each recursive var: eg. in µx.(x,x) we get 2 InvMus
startInvMu m = Leaf m -- the outer µ-binder. We intend to wrap this in successive inverses
invertMu :: InvMu -> Type -> [InvMu]
invertMu inv cur = let
  go cur t = case t of
    THTyCon tycon -> concat -- $ map (\(i , subInvs) -> (\subInv -> InvMu cur i inv) <$> subInvs)
      $ zipWith (\i t -> invertMu (InvMu cur i inv) t) [0..] $
      case tycon of -- the order for tycon branches is important:
        THArrow ars r -> (r : ars)
        THSumTy tys   -> BSM.elems tys
        THProduct tys -> BSM.elems tys
        THTuple tys   -> V.toList tys
    THMu m t    -> [inv] -- [Leaf m]
    THMuBound m -> [inv] -- [Leaf m]
    _ -> [] -- no mus in cur branch
  in case cur of
  TyGround gs  -> concat (go cur <$> gs)
  TyVars vs gs -> concat (go cur <$> gs)
  TyVar v -> []

-- test if an inverted Mu matches the next layer (a potential unrolling of the µ)
-- This happens after type simplifications so there should be no tvars (besides escaped ones)
-- Either (more wrappings to test) (end , True if wrapping is an unrolling)
testWrapper :: InvMu -> Int -> Type -> Either InvMu Bool
testWrapper (Leaf m) recBranch t = Right True
testWrapper (InvMu this r parent) recBranch t | r /= recBranch = Right False
testWrapper (InvMu this r parent) recBranch t = case {-d_ (recBranch , this , parent)-} (this , t) of
  (TyGround g1 , TyGround g2) -> let
    partitionTyCons g = (\(t , o) -> ((\case {THTyCon tycon -> tycon ; _ -> error "wtf" }) <$> t , o))
      $ partition (\case {THTyCon{}->True;_->False}) g
    ((t1 , o1) , (t2 , o2)) = (partitionTyCons g1 , partitionTyCons g2)
    testGuarded t1 t2 = let go i t1 t2 = if i == recBranch then True else t1 == t2
      in zipWith3 go [0..] t1 t2
    muFail = case (t1 , t2) of
      ([THArrow a1 r1] , [THArrow a2 r2]) -> testGuarded (r1 : a1) (r2 : a2)
      ([THSumTy t1   ] , [THSumTy t2   ]) -> testGuarded (BSM.elems t1) (BSM.elems t2)
      ([THProduct t1 ] , [THProduct t2 ]) -> testGuarded (BSM.elems t1) (BSM.elems t2)
      ([THTuple t1   ] , [THTuple t2   ]) -> testGuarded (V.toList t1) (V.toList t2)
      _ -> [False]
    in if not (all identity muFail) {-|| o1 /= o2-} then Right False
       else case parent of
         Leaf{}    -> Right True
         nextInvMu -> Left nextInvMu
  _ -> Right False
-- TODO TyVars (presumably only relevant for let-bindings)
