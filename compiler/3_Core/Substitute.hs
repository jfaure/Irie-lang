-- Biunfication only records type bounds
-- At|during generalisation substitute all type variables
module Substitute (substTVars) where
import CoreSyn
import CoreUtils
import TypeCheck
import TCState
import Control.Lens
import Data.List (partition)
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import qualified Data.Vector.Mutable as MV

-- substTVars: recursively substitute type vars, insert foralls and μ binders, simplify types
-- Simplifications:
--  * ? A -> A & Int =? Int -> Int
--  * remove polar variables `a&int -> int` => int->int ; `int -> a` => `int -> bot`
--  * unify inseparable variables (co-occurence `a&b -> a|b` and indistinguishables `a->b->a|b`)
--  * remove variables that contain the same upper and lower bound (a<:t and t<:a)`a&int->a|int`
--  * roll up recursive types
--
--  1. read all unguarded vars , return var-loops | empty vars and tycons
--  2. check if any in the var loops should be generalised
--  3. mark vars as guarded and substitute guarded types
-- could use a bitvector instead of IntSet since typevars are bounded naturals
substTVars :: IName -> TCEnv s Type
substTVars recTVar = do
  when global_debug (traceM $ "Subst: " <> show recTVar)
  liftMu .= Nothing
  markOccurs True recTVar
--simplifyVars True recTVar
  raw <- substTypeVar True recTVar IS.empty IS.empty
  use quants <&> \q -> if q > 0 then [THBi q raw] else raw

markOccurs pos v = use bis >>= \b -> let
  markType   pos = mapM_ (markTyHead pos)
  markTyHead pos = \case
    THVar v   -> markOccurs pos v -- dupVar pos v
    THBi b ty -> markType pos ty
    THMu x ty -> markType pos ty
    THTyCon t -> case t of
      THArrow ars r -> traverse_ (markType (not pos)) ars *> markType pos r
      THProduct   r -> traverse_ (markType pos) r
      THSumTy     r -> traverse_ (markType pos) r
      THTuple     r -> traverse_ (markType pos) r
    x -> pure ()
--substVar pos v (BiSub pty mty pq mq) = use bis >>= \b -> case if pos then pty else mty of
--  [THVar y] | y /= v && (pos && pq == 0 || mq == 0) -> MV.modify b (over (if pos then pQ else mQ) (\x->x-1)) v *> MV.read b y >>= substVar pos y
--  x -> pure x -- <$ dupVar pos v
  in MV.read b v >>= \bisub@(BiSub pty mty pq mq) -> do
--  t <- substVar pos v bisub
    let t = if pos then pty else mty
--  MV.modify b (over (if pos then pSub else mSub) (const t)) v
    dupVar pos v
    when ((if pos then pq else mq) == 0) (markType pos t)

shouldGeneralise pos bisub@(BiSub pty mty pq mq) = (if pos then mq else pq) > 0
-- && case if pos then (mty,pq) else (pty,mq) of { ([],n) -> n > 0 ; _ -> False }

-- commit to generalising a type variable
generaliseVar pos vars v bisub@(BiSub pty mty pq mq) = quants <<%= (+1) >>= \q -> do
  when global_debug $ traceM $ show v <> " " <> show pos <> " =∀" <> show q <> " " <> show bisub
--MV.modify vars (\(BiSub p m qp qm) -> BiSub (THBound q:p) (THBound q:m) qp qm) v
  MV.modify vars (\(BiSub p m qp qm) -> BiSub [THBound q] [THBound q] qp qm) v
  pure [THBound q] --(if pos then _pSub else _mSub) <$> MV.read vars v

addPiBound pos vars v = MV.read vars v >>= \bisub@(BiSub pty mty pq mq) -> --d_ (show v <> show pos <> show bisub :: Text) $ pure []
--if shouldGeneralise pos bisub then generaliseVar pos vars v bisub else pure []
  case if pos then mty else pty of
    t@[THBound q] -> pure t -- $ if pos then pty else mty
    [THVar v] | [THVar y] <- if pos then pty else mty , y == v -> pure []
    x -> if shouldGeneralise pos bisub then generaliseVar pos vars v bisub else pure []

genVarLoop :: Bool -> [IName] -> TCEnv s Type
genVarLoop pos vars = use bis >>= \b -> ((\v -> (v,) <$> MV.read b v) `mapM` vars)
  >>= \bs -> case find (shouldGeneralise pos . snd) bs of
  Nothing -> pure []
  Just (first , bisub) -> do
    let varsIS = IS.fromList vars
    v <- addPiBound pos b first

    -- Co-occurence analysis; find and remove generalisables that polar co-occur with this 'v'
    -- eg. foldr : (A → (C & B) → B) → C → μx.[Cons : {A , x} | Nil : {}] → (B & C)
    --     foldr : (A → B → B) → B → μx.[Cons : {A , x} | Nil : {}] → B
    let getVars = map (\(THVar i) -> i) . filter (\case { THVar{}->True; _->False})
    let go (l , r) v = MV.read b v >>= \(BiSub p m qp qm) -> pure $ --MV.write b v (BiSub (THBound q : p) (THBound q : m) qp qm) $>
          ((IS.fromList (getVars p) IS.\\ varsIS) `IS.union` l , (IS.fromList (getVars m) IS.\\ varsIS) `IS.union` r)
    (cooccurL , cooccurR) <- foldM go (IS.empty,IS.empty) vars
    IS.toList (cooccurL `IS.difference` cooccurR) `forM` \i ->
--    MV.modify b (\(BiSub p m qp qm) -> BiSub [THBound q] [THBound q] qp qm) i
      MV.modify b (\(BiSub p m qp qm) -> BiSub p m 0 0) i -- zero out occurences
    pure v

substTypeVar pos v loops guarded = use bis >>= \b -> let
--dbgUpdate x = d_ (show x <> " => " <> show t :: Text) t))
  updateVar t = t <$ MV.modify b (over (if pos then pSub else mSub) (const t)) v -- dbgUpdate
  in updateVar =<< if IS.member v loops -- varloop
  then genVarLoop pos (IS.toList loops)
  else if IS.member v guarded -- recursive type
    then mus <<%= (+1) >>= \m -> [THMuBound m] <$ (muEqui %= (IM.insert v m))
    else (MV.read b v) >>= \bisub@(BiSub pty mty pq mq) -> {-d_ (show pos <> show bisub :: Text) $-} let loops' = IS.insert v loops
      in case (if pos then _pSub bisub else _mSub bisub) of
      [] -> genVarLoop pos (IS.toList loops')
      ty' -> do
        -- Check the opposite polarity (if this variable's opposite would be generalised later, it can't be ignored now)
        -- It will generalise if it is [] and has presence at both polarities
        ty <- (++ty') <$> case (if pos then (mty,pq) else (pty,mq)) of { ([],n) | n>0 -> addPiBound (pos) b v ; _ -> pure [] }
--      ty <- pure ty'
        rawT <- substTypeMerge pos loops' guarded ty
        let addMu t = maybe (pure t) (addMuBind rawT t) -- maybe t (\x -> [THMuBind x t])
        mus .= 0
        musCur <- muEqui <<%= (\m -> foldr IM.delete m (IS.toList loops'))
        mergeTypes [] <$> foldM addMu rawT ((musCur IM.!?) <$> IS.toList loops')

insertMu x t = let
  -- Note. [y & µx._] means y and x are the same recursive type
  -- µx.µy. = µx. ; y and x are the same
  rmMuBound x = filter (\case { THMuBound y -> False ; _ -> True })
  rmOuterMus x t = case t of
    THMu y t -> let (xs , ts) = unzip $ rmOuterMus x <$> t in (min y (minimum xs) , concat ts)
    t        -> (x , [t])
  (x' , t') = unzip $ rmOuterMus x <$> rmMuBound x t
  in [THMu (minimum x') (concat t')]

addMuBind rawT guarded x = do
  let (mTypes , other) = partition (\case { THMuBound i->True ; _->False }) rawT
      mbound = (\(THMuBound i) -> i) <$> mTypes
  mn <- muNest <<%= (IM.union (IM.fromList $ ( , (x , other)) <$> mbound))
  r <- case mn IM.!? x of -- can we replace t with subT (a tighter recursive type)
    Just (y , subT) | True <- check _ mempty mempty other subT -> pure (insertMu y subT)-- [THMu y subT]
    _ -> pure (insertMu x guarded)-- [THMu x guarded]
  liftMu .= (Just r)
  pure r

hashCons t = use liftMu <&> \case
  Just mt | True <- check _ mempty mempty [THTyCon t] mt -> mt
  _ -> [THTyCon t]

substTypeMerge :: Bool -> IS.IntSet -> IS.IntSet -> Type -> TCEnv s Type
substTypeMerge pos loops guarded ty = fmap ({-nullLattice pos .-} foldr mergeTypes []) $ ty `forM` let
  substGuarded p = fmap (nullLattice pos . mergeTypes []) . substTypeMerge p IS.empty (IS.union guarded loops)
  in  \case
  THVar x   -> substTypeVar pos x loops guarded
  THBi b ty -> (\t->[THBi b t]) <$> substGuarded pos ty
  THMu x ty -> (\t->insertMu x t) <$> substGuarded pos ty
  THTyCon t -> hashCons =<< case t of
    THArrow ars r -> THArrow   <$> traverse (substGuarded (not pos)) ars <*> substGuarded pos r
    THProduct   r -> THProduct <$> traverse (substGuarded pos) r
    THSumTy     r -> THSumTy   <$> traverse (substGuarded pos) r
    THTuple     r -> THTuple   <$> traverse (substGuarded pos) r
  x -> pure [x]
