module TypeCheck (check) where
import Prim
import CoreSyn as C
import TCState
import PrettyCore
import Externs
import TTCalculus
import qualified Data.Vector as V
import qualified BitSetMap as BSM

-- Biunification solves constraints `t+ <= t-` whereas subsumption compares t+ <:? t+
-- Type annotations may be subtypes (less general) than inferred signatures
-- Check must fill in any holes present in the type annotation
check :: (ExternVar -> TCEnv s Expr) -> Externs -> Type -> Type -> TCEnv s Bool
check handleExtern e inferred gotRaw = let
  go = check' handleExtern e inferred gotRaw
  in if global_debug -- True {-debug getGlobalFlags-}
  then trace ("check: " <> prettyTyRaw inferred <> "\n   <?: " <> prettyTyRaw gotRaw) go else go

check' :: (ExternVar -> TCEnv s Expr) -> Externs -> Type -> Type -> TCEnv s Bool
check' handleExtern es (TyGround inferred) (TyGround gotTy) = let
  readExt x = case readPrimExtern es x of
    c@Core{} -> error $ "type expected, got: " <> show c
    Ty t -> t
  dbgCheck inferred gotTy = identity --trace (prettyTyRaw (TyGround [inferred]) <> " <?: " <> prettyTyRaw (TyGround [gotTy])) 
  checkAtomic :: (ExternVar -> TCEnv s Expr) -> TyHead -> TyHead -> TCEnv s Bool
  checkAtomic handleExtern inferred gotTy = let
    check'' = check' handleExtern es
    end x = if x then pure True else d_ (inferred , gotTy) (pure False)
    in case dbgCheck inferred gotTy (inferred , gotTy) of
    (_ , THTop) -> end True
    (THBot , _) -> end True
    (THExt i , t)  -> check'' (readExt i) (TyGround [t])
    (t , THExt i)  -> check'' (TyGround [t]) (readExt i)
    (THBound x , THBound y)     -> pure $ x == y
    (THMuBound x , THMuBound y) -> pure $ x == y
    (THBi b1 x , THBi b2 y) -> if b1 == b2 then check'' x y else end False
    (THSet l1, THSet l2)  -> end $ l1 <= l2
--  (THSet 0 , x)         -> end True
--  (x , THSet 0)         -> end True
    (THPrim x , THPrim y) -> end $ x `primSubtypeOf` y
    (THMu x _ , THMuBound y) -> end $ y == x
    (THTyCon t1 , THTyCon t2) -> case (t1,t2) of
      (THArrow a1 r1 , THArrow a2 r2) -> let -- differing arities may still match via currying
        go (x:xs) (y:ys) = (&&) <$> check'' y x <*> go xs ys
        go [] [] = check'' r1 r2
        go [] y  = check'' r1 (TyGround [THTyCon $ THArrow y r2])
        go x []  = check'' (TyGround [THTyCon $ THArrow x r1]) r2
        in go a1 a2
--    (THSumTy x , THSumTy y)     -> allM (\case { (k , These a b) -> check'' a b ; _ -> pure False }) $ BSM.toList (align x y)
--    (THProduct x , THProduct y) -> allM (\case { (k , These a b) -> check'' a b ; _ -> pure False }) $ BSM.toList (align x y)
--    Check the annotation is exactly the same size as the inferred type
      (THSumTy x , THSumTy y)     -> let inter = BSM.elems (BSM.intersectionWith check'' x y)
        in if V.length inter == BSM.size x && BSM.size x == BSM.size y then all identity <$> sequence inter else pure False
      (THProduct x , THProduct y) -> let inter = BSM.elems (BSM.intersectionWith check'' x y)
        in if V.length inter == BSM.size x && BSM.size x == BSM.size y then all identity <$> sequence inter else pure False
      (THTuple x , THTuple y)     -> allM (\case { These a b -> check'' a b ; _ -> pure False }) $ V.toList (align x y)
      _ -> end False

    -- for cases that reduce to `x <:? ⊤`
    (a , THMu m b) -> check'' (TyGround [a]) b
    (THMu m a , b) -> check'' a (TyGround [b])
    x -> end False
  in case inferred of
  []   -> pure False
  tys  -> allM (\t -> anyM (checkAtomic handleExtern t) gotTy) $ tys

check' handleExtern es t1 (TyGround [THTop]) = pure True
check' handleExtern es t1@(TyIndexed{}) t2 = normaliseType handleExtern mempty t1 >>= \case
  loop@TyIndexed{} -> error $ "cannot normalise TyIndexed: " <> show loop
  unaliased        -> check' handleExtern es unaliased t2
--check' handleExtern es t1 t2@(TyAlias{}) = normaliseType handleExtern mempty t2 >>= \unaliased ->
--  check' handleExtern es t1 unaliased

check' handleExtern es t1 t2 = error $ show (t1 , t2)

{-
alignMu :: Int -> TyHead -> TyHead -> TyHead -> Bool
alignMu x target lty muBound = (if global_debug
  then trace (prettyTyRaw [lty] <> " µ=? " <> prettyTyRaw [muBound] <> " (" <> prettyTyRaw [target] <> ")")
  else identity) $ let
  exactAlign :: Semialign f => f [TyHead] -> f [TyHead] -> f Bool
  exactAlign = let
    aligner [a] [b] = alignMu x target a b
    aligner a   b   = trace ("typejoin in mu: " <> prettyTyRaw a <> " µ<? " <> prettyTyRaw b) False
    in alignWith (these (const False) (const False) (aligner))
--alignL     = alignWith (these (const True) (const False) (\[a] [b] -> alignMu x target a b))
  in case (lty , muBound) of
  (THTyCon (THProduct lt) , THTyCon (THProduct rt)) -> all identity $ exactAlign lt rt
  (THTyCon (THSumTy   lt) , THTyCon (THSumTy   rt)) -> all identity $ exactAlign lt rt -- alignL rt lt
  (THTyCon (THTuple   lt) , THTyCon (THTuple   rt)) -> all identity $ exactAlign lt rt
--(THTyCon (THSumTy lt) , THTyCon (THSumTy rt)) -> exactAlign lt rt
  (THPrim l , THPrim r) -> l == r -- must be exactly equal to roll up mus
  (a , b) -> check _ mempty mempty [a] [b]
--_ -> False
-}
