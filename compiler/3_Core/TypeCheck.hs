module TypeCheck (check) where
import Prim
import CoreSyn as C
import CoreUtils
import TCState
import Builtins (readPrimType)
import qualified Data.Vector as V
import qualified BitSetMap as BSM

-- Biunification solves constraints `t+ <= t-` whereas subsumption compares t+ <:? t+
-- Type annotations may be subtypes (less general) than inferred signatures
-- Check must fill in any holes present in the type annotation

--Subsumption with subtyping is harder, as it requires checking that for every instance of the user-annotated type, there exists a compatible instance of the inferred one. (A ∀∃… question, not just a ∃)
--The point of initiality and distributivity of ⊓ and ⊔ over → and × is to enable a solution for subsumption

checkAtomic :: forall s. TyHead -> TyHead -> TCEnv s Bool
checkAtomic inferred gotTy = let
  readExt x = case readPrimType x of
    Core (Ty t) _ -> t
    c -> error $ "expected type, got: " <> show c
  end x = pure x -- d_ (inferred , gotTy) False
  in case (inferred , gotTy) of --trace (prettyTyRaw (TyGround [inferred]) <> " <?: " <> prettyTyRaw (TyGround [gotTy]))
  (_ , THTop) -> end True
  (THBot , _) -> end True
  (THExt i , t)  -> check (readExt i) (TyGround [t])
  (t , THExt i)  -> check (TyGround [t]) (readExt i)
  (THAlias q0 , THAlias q) | q0 == q -> pure True
  (i , THAlias q) -> resolveTypeQName q >>= \g -> check (tHeadToTy i) g
  (THAlias q , g) -> resolveTypeQName q >>= \i -> check i (tHeadToTy g)

  (THBound x , THBound y)     -> pure (x == y)
  (THMuBound x , THMuBound y) -> pure (x == y)
  (THBi b1 x , THBi b2 y) -> if b1 == b2 then check x y else end False
  (THPrim x , THPrim y) -> end (x `primSubtypeOf` y)
  (THMu x _ , THMuBound y) -> end $ y == x
  (THTyCon t1 , THTyCon t2) -> case (t1,t2) of
    (THArrow a1 r1 , THArrow a2 r2) -> let -- differing arities may still match via currying
      go (x:xs) (y:ys) = (&&) <$> check y x <*> go xs ys
      go [] [] = check r1 r2
      go [] y  = check r1 (TyGround [THTyCon (THArrow y r2)])
      go x []  = check (TyGround [THTyCon (THArrow x r1)]) r2
      in go a1 a2
--  (THSumTy x , THSumTy y)     -> allM (\case { (k , These a b) -> check' a b ; _ -> pure False }) $ BSM.toList (align x y)
--  (THProduct x , THProduct y) -> allM (\case { (k , These a b) -> check' a b ; _ -> pure False }) $ BSM.toList (align x y)
--  Check the annotation is exactly the same size as the inferred type
    (THSumTy x , THSumTy y)     -> let inter = BSM.elems (BSM.intersectionWith check x y)
      in if V.length inter == BSM.size x && BSM.size x == BSM.size y then all identity <$> sequence inter else pure False
    (THProduct x , THProduct y) -> let inter = BSM.elems (BSM.intersectionWith check x y)
      in if V.length inter == BSM.size x && BSM.size x == BSM.size y then all identity <$> sequence inter else pure False
    (THTuple x , THTuple y) -> allM (\case { These a b -> check a b ; _ -> pure False }) $ V.toList (align x y)
    _ -> end False

  -- for cases that reduce to `x <:? ⊤`
  (a , THMu _ b) -> check (TyGround [a]) b
  (THMu _ a , b) -> check a (TyGround [b])
  _ -> end False

check :: forall s. Type -> Type -> TCEnv s Bool
check inf got = let
  --trace ("check: " <> prettyTyRaw inf <> "\n   <?: " <> prettyTyRaw got) $
  in case (inf , got) of
  (TyGround inferred , TyGround gotTy)  -> allM (\t -> anyM (checkAtomic t) gotTy) inferred
  (t1 , t2) -> error $ show t1 <> "\n" <> show t2
