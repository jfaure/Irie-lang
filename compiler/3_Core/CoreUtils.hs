module CoreUtils where
----------------------------------------------------
-- Various utility functions operating on CoreSyn --
----------------------------------------------------
-- Any function that could be given in CoreSyn directly is found here
import CoreSyn
import ShowCore()
import PrettyCore
import Prim
import Data.List (partition)
import qualified BitSetMap as BSM
import qualified Data.Vector as V

isPoisonExpr ∷ Expr → Bool = (\case { PoisonExpr → True ; _ → False })

mapType ∷ (TyHead → TyHead) → Type → Type
mapType f = let
  go = \case
    THTyCon tcon → f $ THTyCon $ case tcon of
      THArrow ars r → THArrow   (mapType f <$> ars) (mapType f r)
      THSumTy a     → THSumTy   (mapType f <$> a)
      THProduct a   → THProduct (mapType f <$> a)
      THTuple a     → THTuple   (mapType f <$> a)
    th → f th
  in \case
  TyGround gs → TyGround (go <$> gs)
  TyVars v gs → TyVars v (go <$> gs)
  TyVar v → TyVar v

{-
-- eqTypes a b = all identity (zipWith eqTyHeads a b) -- not zipwith !
eqTypes (TyGround a) (TyGround b) = all identity (alignWith (these (const False) (const False) eqTyHeads) a b)

eqTyHeads a b = kindOf a == kindOf b && case (a,b) of
  (THPrim a  , THPrim b)  → a == b
  (THMuBound m  , THMu n _)  → m == n
  (THMu n _ , THMuBound m)  → m == n
  (THTyCon a , THTyCon b) → case (a,b) of
--  (THSumTy a , THSumTy b) → and $ BSM.elems $ alignWith (these (const False) (const False) eqTypes) a b
    (THSumTy a , THSumTy b)     → and $ BSM.elems $ BSM.intersectionWith eqTypes a b
    (THProduct a , THProduct b) → and $ BSM.elems $ BSM.intersectionWith eqTypes a b
    (THTuple a , THTuple b) → and $ V.zipWith eqTypes a b
  (THBound a , THBound b) → a == b
  _ → False
-}

partitionType ∷ Type → (BitSet , GroundType)
partitionType = \case
  TyVars vs g → (vs , g)
  TyGround g  → (0  , g)
  TyVar v     → (0 `setBit` v , [])
--pi@TyPi{}   → (0 , [pi]) -- TODO ok?
--TyIndexed{} → _
  t → error $ show t

tyLatticeEmpty pos = \case
  TyGround [] → TyGround [if pos then THBot else THTop] -- pure ty
  t  → t

hasVar t v = case t of
  TyGround{}  → False
  TyVar w     → v == w
  TyVars vs g → testBit vs v

--mkTHArrow ∷ [[TyHead]] → [TyHead] → Type
mkTyArrow args retTy = [THTyCon $ THArrow args retTy]

getArrowArgs = \case
  TyGround [THTyCon (THArrow as r)] → (as , r)
  TyGround [THBi i t] → getArrowArgs t
  t → trace ("not a function type: " <> prettyTyRaw t) ([] , t)

-- appendArrowArgs [] = identity
-- appendArrowArgs args = \case
--   [THTyCon (THArrow as r)] → [THTyCon $ THArrow (as ++ args) r]
--   [THPi (Pi p t)]   → [THPi (Pi p $ appendArrowArgs args t)]
--   [THSi (Pi p t) _] → [THPi (Pi p $ appendArrowArgs args t)]
--   [THBi i t] → [THBi i $ appendArrowArgs args t]
--   x → [THTyCon $ THArrow args x]

prependArrowArgs ∷ [[TyHead]] → [TyHead] → [TyHead]
prependArrowArgs [] = identity
prependArrowArgs args = \case
  [THTyCon (THArrow as r)] → [THTyCon $ THArrow ((TyGround <$> args) ++ as) r]
  [THBi i (TyGround t)] → [THBi i $ TyGround $ prependArrowArgs args t]
  x → [THTyCon $ THArrow (TyGround <$> args) (TyGround x)]

prependArrowArgsTy ∷ [Type] → Type → Type
prependArrowArgsTy [] = identity
prependArrowArgsTy args = \case
  TyGround [THTyCon (THArrow as r)] → TyGround [THTyCon $ THArrow (args ++ as) r]
  TyGround [THBi i t] → TyGround [THBi i $ prependArrowArgsTy args t]
  x → TyGround [THTyCon $ THArrow args x]

isTyCon = \case
 THTyCon{} → True
 _         → False

tyOfTy ∷ Type → Type
tyOfTy t = TyGround [THSet 0]

tyExpr = \case -- get the type from an expr.
  Ty t → Just t
  Core e t → Just (TyTerm e t)
  expr → Nothing --error $ "expected type, got: " ++ show expr

tyOfExpr = \case
  Core _x ty → ty
  Ty t       → tyOfTy t
  PoisonExpr → TyGround []
  m@MFExpr{} → error $ "unexpected mfexpr: " <> show m

-- expr2Ty ∷ _ → Expr → TCEnv s Type
-- Expression is a type (eg. untyped lambda calculus is both a valid term and type)
expr2Ty _judgeBind e = case e of
 Ty x → pure x
 Core c _ty → case c of
-- Var (VBind i) → pure [THRecSi i []]
   Var (VArg x)  → pure $ TyVar x --[THVar x] -- TODO ?!
-- App (Var (VBind fName)) args → pure [THRecSi fName args]
   x → error $ "raw term cannot be a type: " ++ show e
 PoisonExpr → pure $ TyGround [THPoison]
 x → error $ "raw term cannot be a type: " ++ show x

bind2Expr = \case
  BindOK isRec e   → e
  LetBound isRec e → e
  BindOpt _ _ e    → e
  x → error (show x)

------------------------
-- Type Manipulations --
------------------------
--eqTyHead a b = kindOf a == kindOf b
kindOf = \case
  THPrim p  → KPrim p
  THTyCon t → case t of
    THArrow{}   → KArrow
    THProduct{} → KProd
    THSumTy{}   → KSum
    THSumOpen{} → KSum
    THTuple{}   → KTuple
  THBound{} → KBound
  THMuBound{} → KRec
  THMu{}      → KRec
  _ → KAny

mergeTyUnions ∷ Bool → [TyHead] → [TyHead] → [TyHead]
mergeTyUnions pos l1 l2 = let
  cmp a b = case (a,b) of
    (THBound a' , THBound b') → compare a' b'
    (THMu m t , THMuBound n) → compare m n
    (THMuBound n , THMu m t) → compare m n
    _ → (kindOf a) `compare` (kindOf b)
  in foldr (mergeTyHeadType pos) [] (sortBy cmp $ l2 ++ l1)

mergeTyHeadType ∷ Bool → TyHead → [TyHead] → [TyHead]
mergeTyHeadType pos newTy = \case
  []       → [newTy]
  ty : tys → mergeTyHead pos newTy ty ++ tys

mergeTyHead ∷ Bool → TyHead → TyHead → [TyHead]
mergeTyHead pos t1 t2 = --(\ret → trace (prettyTyRaw (TyGround [t1]) <> " ~~ " <> prettyTyRaw (TyGround [t2]) <> " => " <> prettyTyRaw (TyGround ret)) ret) $
  let join = [t1 , t2]
      zM  ∷ Semialign f ⇒ Bool → f Type → f Type → f Type
      zM pos' = alignWith (these identity identity (mergeTypes pos'))
      mT = mergeTypes pos
  in case join of
  [THTop , THTop] → [THTop]
  [THBot , THBot] → [THBot]
  [THSet a , THSet b] → [THSet $ max a b]
  [THPrim a , THPrim b]  → if a == b then [t1] else case (a,b) of
--  (PrimInt x , PrimInt y) → [THPrim $ PrimInt $ max x y]
    (PrimBigInt , PrimInt _) → [THPrim $ PrimBigInt]
    (PrimInt _ , PrimBigInt) → [THPrim $ PrimBigInt]
    _ → join

--[THMu m a , THMuBound n] → if m == n then [t1] else join
--[THMuBound n , THMu m a] → if m == n then [t2] else join
  [THMu m _ , THBound n]  → if m == n then [t1] else join
  [THBound n , THMu m _]  → if m == n then [t2] else join
  [THMu m mt , THMu n nt] → if m == n then [THMu m (mergeTypes pos mt nt)] else join
  [THBi m mt , THBi n nt] → if m == n then [THBi m (mergeTypes pos mt nt)] else join -- TODO slightly dodgy
  [THMuBound a , THMuBound b] → if a == b then [t1] else join

  [THBound a , THBound b]     → if a == b then [t1] else join
  [THPrim (PrimInt 32) , THExt 1] → [t1] -- HACK
  [THExt a , THExt  b]        → if a == b then [t1] else join
  [THTyCon t1 , THTyCon t2]   → case [t1,t2] of
--  [THSumTy a   , THSumTy b]   → [THTyCon $ THSumTy   $ if pos then BSM.intersectionWith mT a b else BSM.unionWith mT a b]
    [THSumTy a   , THSumTy b]   → [THTyCon $ THSumTy   $ BSM.unionWith mT a b]
    [THProduct a , THProduct b] → [THTyCon $ THProduct $ if pos then BSM.unionWith mT a b else BSM.intersectionWith mT a b]
    [THTuple a , THTuple b]     → [THTyCon $ THTuple (zM pos a b)]
    [THArrow d1 r1 , THArrow d2 r2] | length d1 == length d2 → [THTyCon $ THArrow (zM (not pos) d1 d2) (mergeTypes pos r1 r2)]
    _ → join
  _ → join

nullType = \case
  TyVars 0 [] → True
  TyGround [] → True
  _ → False

mergeTypeList ∷ Bool → [Type] → Type
mergeTypeList pos ts = let r = foldr (mergeTypes pos) (TyGround []) ts
  in r -- trace (T.intercalate " , " (prettyTyRaw <$> ts) <> " ⇒ " <> prettyTyRaw r) r

rmMuBound m = let goGround = filter (\case { THMuBound x → x /= m ; _ → True }) in \case
  TyGround g  → TyGround (goGround g)
  TyVars vs g → TyVars vs (goGround g)
  t → t

rmTVar v = \case
  TyVar w     → if w == v then TyGround [] else TyVar w
  TyVars ws g → TyVars (ws `clearBit` v) g
  TyGround g  → TyGround g

mergeTVars vs = \case
  TyVar w     → TyVars (vs `setBit` w) []
  TyVars ws g → TyVars (ws .|. vs) g
  TyGround g  → TyVars vs g
mergeTypeGroundType pos a b = mergeTypes pos a (TyGround b)
mergeTVar v = \case
  TyVar w     → TyVars (setBit 0 w `setBit` v) []
  TyVars ws g → TyVars (ws `setBit` v) g
  TyGround g  → TyVars (0  `setBit` v) g
mergeTypes pos (TyGround a) (TyGround b)     = TyGround (mergeTyUnions pos a b)
mergeTypes pos (TyVar v) t                   = mergeTVar v t
mergeTypes pos t (TyVar v)                   = mergeTVar v t
mergeTypes pos (TyVars vs g1) (TyVars ws g2) = TyVars (vs .|. ws) (mergeTyUnions pos g1 g2)
mergeTypes pos (TyVars vs g1) (TyGround g2)  = TyVars vs (mergeTyUnions pos g1 g2)
mergeTypes pos (TyGround g1) (TyVars vs g2)  = TyVars vs (mergeTyUnions pos g1 g2)
mergeTypes pos a b = error $ "attempt to merge weird types at " <> if pos then "+" else "-" <> ": " <> show (a , b)

-- TODO check at the same time if this did anything
mergeTysNoop ∷ Bool → Type → Type → Maybe Type = \pos a b → Just $ mergeTypes pos a b

-- Test if µ wrappers are unrollings of the recursive type `see eg. mapFold f l = foldr (\x xs ⇒ Cons (f x) xs) Nil l`
--    [Cons : {A , µC.[Cons : {A , µC} | Nil : {}]} | Nil : {}]
-- ⇒ µC.[Cons : {A , µC} | Nil : {}]
-- To do this pre-process the µ by 'inverting' it so we can incrementally test layers
-- This 'is' a zipper; like the cursor in a text editor or the pwd in a file system
data InvMu
  = Leaf IName
  | InvMu
  { this      ∷ Type  -- A subtree of the µ. test
  , recBranch ∷ Int
  , parent    ∷ InvMu -- Nothing if root
  } deriving Show

-- i is the wrapping tycon branch we recursed into to get here
-- ie. it should be ignored when testing if the parent layer is an unrolling of this µ
-- [InvMu]: one for each recursive var: eg. in µx.(x,x) we get 2 InvMus
startInvMu m = Leaf m -- the outer µ-binder. We intend to wrap this in successive inverses
invertMu ∷ Int → InvMu → Type → [InvMu]
invertMu muVar inv cur = {-trace (prettyTyRaw cur) $-} let
  go cur t = case t of
    THTyCon tycon → concatMap (\(i , t) → invertMu muVar (InvMu cur i inv) t) $
      case tycon of -- use the keys to indicate recbranch for sum/product, and index for tuple/arrow
        THArrow ars r → zip [0..] (r : ars) -- !ret type is recBranch 0
        THSumTy tys   → BSM.toList tys -- V.toList $ BSM.elems tys
        THProduct tys → BSM.toList tys -- V.toList $ BSM.elems tys
        THTuple tys   → V.toList (V.indexed tys)
    THMu m t    | m == muVar → [inv]
    THMuBound m | m == muVar → [inv]
    _ → [] -- no mus in unguarded type or incorrect mu at leaf
  in case cur of
  -- TODO why are we dropping tvars ?
  TyGround gs   → concatMap (go cur) gs
  TyVars _vs gs → concatMap (go cur) gs
  TyVar _v → []
  x → error (show x)

-- test if an inverted Mu matches the next layer (a potential unrolling of the µ)
-- This happens after type simplifications so there should be no tvars (besides escaped ones)
-- Either (more wrappings to test) (end , True if wrapping is an unrolling)
testWrapper ∷ InvMu → Int → Type → Either InvMu Bool
testWrapper inv recBranch t = case inv of
  Leaf _m             → Right True
  InvMu this r parent → if False && r /= recBranch -- Avoid pointless work if testing against wrong branch
--then d_ (r , recBranch , this) (Right False)
  then Right False
  else case {-d_ (recBranch , parent , this , t)-} (this , t) of
    (TyGround g1 , TyGround g2) → let
      partitionTyCons g = (\(t , o) → ((\case {THTyCon tycon → tycon ; _ → error "wtf" }) <$> t , o))
        $ partition (\case {THTyCon{}→True;_→False}) g
      ((t1 , _o1) , (t2 , _o2)) = (partitionTyCons g1 , partitionTyCons g2)
      testGuarded t1 t2 = V.izipWith (\i t1 t2 → i == recBranch || eqTypesRec t1 t2) t1 t2
      testBSM (i , (t1 , t2)) = i == recBranch || eqTypesRec t1 t2
      muOK = case (t1 , t2) of
        -- TODO roll + merge things like μx.[Cons {A , x & [Nil]} ⇒ μx.[Nil | Cons {A , x}
        ([THArrow a1 r1] , [THArrow a2 r2]) → and $ testGuarded (V.fromList $ r1 : a1) (V.fromList $ r2 : a2)
        ([THSumTy t1   ] , [THSumTy t2   ]) → and $ testBSM <$> BSM.toList (BSM.intersectionWith (,) t1 t2)
        ([THProduct t1 ] , [THProduct t2 ]) → and $ testBSM <$> BSM.toList (BSM.intersectionWith (,) t1 t2) -- TODO HACK not quite right
        ([THTuple t1   ] , [THTuple t2   ]) → and $ testGuarded t1 t2
        _ → False
      in if muOK {-|| o1 /= o2-}
         then case parent of
           Leaf{}    → Right True -- OK found an unrolling
           nextInvMu → Left nextInvMu -- so far OK, more wraps to test
         else Right False
    _ → Right False
-- TODO TyVars (presumably only relevant for let-bindings)

eqTypesRec (TyGround [THMuBound n]) (TyGround [THMu m _]) = m == n
eqTypesRec (TyGround [THMu m _]) (TyGround [THMuBound n]) = m == n
eqTypesRec (TyGround [THMu m t1]) (TyGround [THMu n t2]) =
  t1 == mapType (\case { THMuBound x | x == n → THMuBound m ; x → x }) t2
eqTypesRec t1 t2 = -- trace (prettyTyRaw t1 <> " =? " <> prettyTyRaw t2) $
  t1 == t2
