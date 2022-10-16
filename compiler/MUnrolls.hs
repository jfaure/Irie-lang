{-# Language TypeFamilies , FlexibleInstances , MultiParamTypeClasses , UndecidableInstances , GeneralisedNewtypeDeriving #-}
module MUnrolls where
import Data.Functor.Foldable
import Data.Functor.Base
import Data.Functor.Adjunction
import qualified Data.Functor.Rep as Rep
import Control.Monad.Free
import Control.Comonad
import Control.Comonad.Cofree
import Control.Arrow
import Control.Monad.Fix

-- Control functor F = (A + _)
tailRecurse :: (c -> Either b c) -> c -> b
tailRecurse c = h where h = (identity ||| h) . c -- (|||) = codiagonal

--hyloM :: (Functor f , Monad m , Traversable f) => (f b -> m b) -> (a -> m (f a)) -> a -> m b
--hyloM f g = h where h = f <=< traverse h <=< g
myhylo f g = h where h = f . fmap h . g
-- hylos do not compose together, but compose with algebra and coalgebra homomorphisms
-- thus ((C,c),(a,A)) |-> ((C,c)>->(a,A)) can be tunred into a functor of type (F-Coalg(C))op x F-Alg(C) -> Set
-- post-composing a hylo with any algebra homomorphism h :(a,A) -> (b,B) yields a unique hylo h.(|a <- c|) = (|b <- c|)
-- full subcategory of F-Coalg c of recursive coalgebras is denoted F-Rec c

-- Rolling rule => if base functor is a composition, we can swap them

-- class (Functor f, Representable u) =>
-- Adjunction l r where
--   unit : a -> r (l a)          -- leftAdjunct identity  : ID ->. R . L
--   counit : l (r a) -> a        -- rightAdjunct identity : L . R ->. Id
--   leftAdjunct : (l a -> b) -> a -> r b     -- fmapR f . unit
--   rightAdjunct : (a -> r b) -> l a -> b    -- counit . fmapL f
--   -- fmapL h = rightAdjunct (unit . h)
--   -- fmapR k = leftAdjunct  (k . counit)
-- adjuncts are mutually inverse
-- naturality properties as fusion laws
-- R k . leftAdjunct f . h = leftAdjunct (k . f . L h)
-- k . rightAdjunct g . L h = rightAdjunct (R k . g . h)

--newtype UCo w a = UCo { uCo :: a } deriving Functor -- : G-Coalg C -> C
--instance Comonad g => Adjunction (UCo g) (Cofree g) where -- C <=> G-Coalg C
--  counit = extract
--  unit   = ana -- unfold

-- When the adjunction L -| R is fixed, what remains is the choice of F and G
-- focusing on input, G := D , F := C = L . D . R
-- σ = L . D . η : (L . D ->. C . L) -| τ = η . D . R : (D . R ->. R . C)
-- here the conjugate rule can be simplified,
-- since Rτ a = leftAdjunct a and C x . Lσ c = L (D (leftAdjunct x) . c)
-- =>  x = a . L (D (leftAdjunct x) . c)
-- <=> leftAdjunct x = leftAdjunct a . D (leftAdjunct x) . c

-- Conjugate rule (shunt functors between alg and coalg)
-- instantiated to focus on data functor D
-- canonical control functor C is obtained by circling around: L . D . R
c1,c2 :: (Adjunction l r , Functor d) => (l (d (r b)) -> b) -> (a -> d a) -> l a -> b
c1 a c = h where h = a . fmap{-L-} (fmap{-D-} (leftAdjunct h) . c) -- (3.9)
c2 a c = h where h = rightAdjunct (leftAdjunct a . fmap{-D-} (leftAdjunct h) . c)

-- anaM psi = a where a = fmap embed . traverse a <=< psi
--mc :: (Adjunction l r , Functor d) => (l (d (r b)) -> b) -> (a -> m (d a)) -> l a -> m b
--mc a c = h where -- leftAdjunct : (l a -> b) -> a -> r b
--  h :: l a -> m b
--  h = fmap a . traverse (traverse (leftAdjunct h) <=< c)

-- focus on recursive coalgebras, so x = a . F x . Lσ c
-- equation builds on canonical control functor: c1 = x = a . L (D (leftAdjunct x) . c
-- hyloShift, adjunction Id -| Id. => (| a <- α C . c |) = (| a . α A <- c |)
hyloShift :: Functor d => (Identity (d (Identity b)) -> b) -> (a -> d a) -> Identity a -> b
hyloShift = c1

-- mutu-hylo: Diag -| (x)
-- x = a . split (D (leftAdjunct x) . c) <=> note. a = (a1,a2) and x = (x1,x2)
--   x1 = a1 . D (x1 &&& x2) . c : A1 <- C
--   x2 = a2 . D (x1 &&& x2) . c : A2 <- C
-- zygo-hylo: a2 := a'2 . D outr

-- banana-split
-- Diag satisfies Diag . D = (D x D) . Diag
-- instantiate conjugate rule to F,G := D x D , D
-- (| a1 <- c |) &&& (| a2 <- c |) = (| a1 . D outl &&& a2 . D outr <- c |)
-- since (x)τ(a1,a2) = a1 . D outl &&& a2 . D outr.

-- accu-hylo : _ x P -| (-)^P
-- x = a. ((D (Λ x) . c) x P) : A <- C x P
-- Note! the left adjunct of the curry adjunction is NOT Prelude.curry
-- leftAdjunct = (\f a e -> f (e , a). curry = \f a e -> f (a , e)
accuHylo :: Functor d => ((p , d (p -> b)) -> b) -> (a -> d a) -> (p , a) -> b
accuHylo = c1

-- constant parameters can be modelled with functor strength (<$)
-- x = a . D x . σ C . (c x P)
-- paramHylo' = c1
-- paramHylo a c =
--   h where
--   h = a . fmap{-D-} h . strength . (c *** identity)
--   strength :: Functor d => (d a , p) -> d (a , p)
--   strength (f , p) = fmap (,p) f

-- UG -| CofreeG
-- cofree G-coalgebra , possibly infinite trees with branching structure determined by G
-- and labels drawn from A; the right adjoint of the underlying functor UG
-- The action of CofreeG A = (GInf A , tail A) maps a tree to G-structure of subtrees
newtype UG (g :: * -> *) a = UG { carrier :: a } deriving Functor
newtype CofreeG d r = CofreeG { unGCoalg :: Cofree d r } deriving Functor
instance Functor d => Comonad (CofreeG d) where
  extract = extract . unGCoalg
  duplicate = CofreeG . fmap CofreeG . duplicate . unGCoalg
instance (Comonad g , Rep.Representable (CofreeG g))
  => Adjunction (UG g) (CofreeG g) where
  counit = extract . carrier -- : l (r a) -> a
  unit   = _ -- ana  -- a -> r (l a)
-- f = head B . UG g <=> CofreeG f . [( a )] = g

--histoHylo :: (Functor d , _) => ((Cofree d _) -> _) -> _ -> _ -> c
--histoHylo :: (Functor d, Adjunction w r) =>
--     (w (Cofree d (r c)) -> c) -> (a -> Cofree d a) -> w a -> c
--histoHylo = c1

-- The naive instantiation is slow so an optimised version is given explicitly
dyna :: Functor d => (d (Cofree d c) -> c) -> (a -> d a) -> a -> c
dyna a c = extract . h where h = uncurry (:<) . (a &&& identity) . fmap h . c

acata alg = hylo alg project
aana  coa = hylo embed coa

{-
conjugateHylo :: (Adjunction l m , Adjunction m r , Functor f) => (m (f (r c)) -> c) -> (a -> m (f (l a))) -> a -> c
conjugateHylo a c = rightAdjunct (hylo (leftAdjunct a) (rightAdjunct c)) . unit

adjointFold :: Data.Functor.Foldable.Recursive t => ((t -> a) -> c) -> (b -> Base t a -> a) -> b -> c
adjointFold   rA lA = rA . cata . lA
adjointUnfold rA lA = lA . cata . rA

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
-}

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
