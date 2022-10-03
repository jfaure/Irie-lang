{-# Language TypeFamilies #-}
module MUnrolls where
import Data.Functor.Foldable
import Data.Functor.Base
import qualified Data.Functor.Rep as Rep
import Control.Monad.Free
import Control.Comonad
import Control.Comonad.Cofree
import Control.Arrow
import Control.Monad.Fix

acata alg = hylo alg project
aana  coa = hylo embed coa

adjointFold :: Data.Functor.Foldable.Recursive t => ((t -> a) -> c) -> (b -> Base t a -> a) -> b -> c
adjointFold   rA lA = rA . cata . lA
adjointUnfold rA lA = lA . cata . rA
adjointHylo :: Functor f ⇒ ((a1 -> b) -> a1 -> f a1) -> (t -> f b -> b) -> (a2 -> a1) -> t -> (a1 -> b) -> a2 -> f a1
adjointHylo rightAdjunct leftAdjunct unit alg coalg = rightAdjunct (hylo (leftAdjunct alg) (rightAdjunct coalg)) . unit

lAId f = Identity    . f . Identity
rAId f = runIdentity . f . runIdentity

lACurry f a e     = f (e , a)
rACurry f (e , a) = Rep.index (f a) e

--paramFold :: P.Functor f => (a -> f (a -> b) -> b) -> a -> FixF f -> b
paramFold f = curry (adjointFold lACurry rACurry (uncurry f))
--paramUnfold :: P.Functor f => (b -> a -> f (a, b)) -> b -> a -> FixF f
--paramUnfold = adjointUnfold

newtype KleisliAdjF (m :: * -> *) a = KAF { unKAF :: a }
newtype KleisliAdjG m a = KAG { unKAG :: m a }
lAKleisli (Kleisli f) = KAG . f . KAF
rAKleisli f = Kleisli $ unKAG . f . unKAF

--newtype CokleisliAdjF (w :: Type -> Type) a = CoKAF { unCoKAF :: a }
--instance Comonad w => Functor (CokleisliAdjF w) (->) (Cokleisli w) where
--  fmap f = Cokleisli (CoKAF . f . unCoKAF . extract)
--newtype CokleisliAdjG w a = CoKAG { unCoKAG :: w a }
--instance Comonad w => Functor (CokleisliAdjG w) (Cokleisli w) (->) where
--  fmap (Cokleisli f) = CoKAG . (=>> f) . unCoKAG
--
--unfoldM :: (Traversable f, Monad m) => (b -> m (f b)) -> b -> m (FixF f)
--unfoldM coalg = unKAG . adjointUnfold lAKleisli rAKleisli (KAG . liftM (P.fmap KAF) . coalg)

-- Recursion-schemes
myHisto :: Recursive t => (Base t (Cofree (Base t) a) -> a) -> t -> a
myHisto psi = extract . h where
  h = (\(a , b) → a :< b) . (psi &&& identity) . fmap h . project

myfutu :: Corecursive t => (a -> Base t (Free (Base t) a)) -> a -> t
myfutu psi = embed . fmap worker . psi where
  worker (Pure f) = myfutu psi f
  worker (Free f) = embed (fmap worker f)

--myPrepro :: Corecursive t => (forall b. Base t b -> Base t b) -> (Base t a -> a) -> t -> a
--myPrepro e f = c where c = f . fmap (c . hoist e) . project
--
--myPostpro :: Recursive t => (forall b. Base t b -> Base t b) -> (a -> Base t a) -> a -> t
--myPostpro e g = a where a = embed . fmap (hoist e . a) . g

-- Depth first monadic unrolling with access to images of the unrolling
-- ! probably can avoid mfix
--anaParaM :: (Corecursive t , Traversable (Base t) , Monad m , MonadFix m) =>
--  ((a , Base t t) -> m (Base t a)) -> a -> m t
anaParaM :: (Corecursive t , Traversable (Base t) , Monad m , MonadFix m) =>
  ((a , t) -> m (Base t a)) -> a -> m t
anaParaM psi = a where
  a seed = mfix (\ret → fmap embed $ traverse a =<< psi (seed , ret))

anaM :: (Corecursive t, Traversable (Base t), Monad m) => (a -> m (Base t a)) -> a -> m t
anaM psi = a where a = fmap embed . traverse a <=< psi

apoM :: (Corecursive t, Traversable (Base t), Monad m) => (a -> m (Base t (Either t a))) -> a -> m t
apoM psi = a where a = fmap embed . traverse (pure ||| a) <=< psi

futuM :: (Corecursive t, Traversable (Base t), Monad m) => (a -> m (Base t (Free (Base t) a))) -> a -> m t
futuM psi = f where
  f = fmap embed . traverse worker <=< psi
  worker (Pure g) = f g
  worker (Free g) = embed <$> traverse worker g

hyloM :: (Functor f , Monad m , Traversable f) => (f b -> m b) -> (a -> m (f a)) -> a -> m b
hyloM f g = h where h = f <=< traverse h <=< g

-- cataM . apoM
hypoM :: (Traversable t, Monad m) => (t b -> m b) -> (c -> m (t (Either b c))) -> c -> m b
hypoM f g = h where h = f <=< traverse (pure ||| h) <=< g

-- traverse : (a -> f b) -> t a -> f (t b)
-- anaM psi = a where a = fmap embed . traverse a <=< psi
ganaM :: (Corecursive t, Monad m , Monad n , Traversable (Base t) , Traversable m)
  => (forall b. m (Base t b) -> Base t (m b)) -- a distributive law
  -> (a -> n (Base t (m a)))                  -- a (Base t)-m-coalgebra
  -> a                                        -- seed
  -> n t
ganaM k psi = a . return <=< psi where
  a = fmap embed . traverse a <=< traverse (traverse psi . join) . k

gApoM :: (Corecursive t , Recursive t, Traversable (Base t), Monad m) => (a -> m (Base t (Either t a))) -> a -> m t
gApoM = ganaM distApo
