{-# Language FlexibleInstances , MultiParamTypeClasses , GADTs , RankNTypes , QuantifiedConstraints , PolyKinds , ImpredicativeTypes , DataKinds #-}
module CH where
import Prelude hiding (Product , Sum)
import Data.Functor.Rep
import Data.Functor.Base
import Data.Functor.Sum
import Data.Functor.Product
import Control.Monad.Free
import Control.Comonad
import Control.Comonad.Cofree
import Control.Comonad.Trans.Env
import Control.Arrow
import Data.Functor.Compose
import GHC.Prim

-- hylo Control functor (A + _) models tail recursion
tailRecurse :: (c -> Either a c) -> c -> a
tailRecurse c = h where h = (identity ||| h) . c -- <=> h = (id ||| id) . (A + h) . c

-- Rolling rule: algebras or coalgebras where two functors compose to create base functor
-- = an adjunction like correspondence between 2 types of hylomorphisms
-- there is bijection between sets of hylos:
-- L_ (C , c) >-> (a,A) ~= (C,c) >-> _R (a,A)
-- natural in (C,c) : R.L-Coalg D and (a,A) : L.R-Alg C
-- This is witnessd by la x = R x . c and ra y = a . L y
-- these trivially form a bijection between fixed points of ra . la and of la . ra
-- thus: x = a . L (R x) . L c <=> y = R a . R (L y) . c
-- here f1 is colifted L to coalgebras and f2 is lifted R to algebras
rollLhs :: (Functor f1, Functor f2) =>
  (f1 (f2 b) -> b) -> (a -> f2 (f1 a)) -> f1 a -> b
rollLhs a c = h where h = a . fmap (fmap h) . fmap c

rollRhs :: (Functor f1, Functor f2) =>
  (f2 (f1 b) -> b) -> (a -> f1 (f2 a)) -> a -> f1 b
rollRhs a c = h where h = fmap a . fmap (fmap h) . c

{-
instance Adj w m => Adj (EnvT e w) (ReaderT e m) where
  aunit              = ReaderT . flip fmap EnvT . flip lAdjunct
  acounit (EnvT e w) = rAdjunct (flip runReaderT e) w

instance (Adj f g, Adj f' g') => Adj (Sum f f') (Product g g') where
  aunit a = Pair (lAdjunct InL a) (lAdjunct InR a)
  acounit (InL l) = rAdjunct (\(Pair x _) -> x) l
  acounit (InR r) = rAdjunct (\(Pair _ x) -> x) r
-}

-- iff there is a bijection between the sets of arrows: (natural in both A and B)
-- adjunctL : C(L a -> b) ~= D(A -> R B) : adjunctR
data Adjunction l r = Adjunction
 { aunit     :: forall a.   a -> r (l a)           -- = adjunctL identity
 , counit    :: forall a.   l (r a) -> a           -- = adjunctR identity
 , adjunctL  :: forall a b. (l a -> b) -> a -> r b -- = (\f->fmap f . unit)
 , adjunctR  :: forall a b. (a -> r b) -> l a -> b -- = (\f->counit . fmap f)
 }

-- shortcut to define adjunctions using (unit * counit) | (adjunctL * adjunctR)
mkAdjUnit :: (Functor l , Functor r) =>
  (forall a b. a -> r (l a)) -> (forall a b. l (r a) -> a) -> Adjunction l r
mkAdjUnit unit counit = Adjunction unit counit (\f->fmap f . unit) (\f->counit . fmap f)
mkAdjlArA :: (Functor l , Functor r) =>
  (forall a b. (l a -> b) -> a -> r b) -> (forall a b. (a -> r b) -> l a -> b) -> Adjunction l r 
mkAdjlArA lA rA = Adjunction (lA identity) (rA identity) lA rA

-- Adjoint functors give rise to a monad: unit = aunit ,  join = fmap counit and bind:
adjBind :: (Functor f1, Functor l, Functor r, Functor f2) =>
     Adjunction l r -> f1 (f2 a) -> (a -> b) -> f1 (r (l (f2 b)))
adjBind a = \x f -> fmap (aunit a) (fmap (fmap f) x)

-- | A right adjoint functor admits an intrinsic notion of zipping
zipR :: Adjunction f u -> (u a , u b) -> u (a , b)
zipR a = adjunctL a (adjunctR a fst &&& adjunctR a snd)

splitL :: Adjunction f u -> f a -> (a, f ())
splitL a = adjunctR a (flip (adjunctL a) () . (,))

unsplitL :: Functor f => a -> f () -> f a
unsplitL = (<$)

-- | Every functor in Haskell permits unzipping
unzipR :: Functor u => u (a, b) -> (u a, u b)
unzipR = fmap fst &&& fmap snd

adjCompose :: ( Functor l , Functor r , Functor l' , Functor r')
  => Adjunction l r -> Adjunction l' r' -> Adjunction (Compose l l') (Compose r' r)
adjCompose
  (Adjunction { adjunctL = la  , adjunctR = ra})
  (Adjunction { adjunctL = la' , adjunctR = ra'})
  = mkAdjUnit (Compose . la' (la Compose)) (ra (ra' getCompose) . getCompose)
--  (Compose . fmap (fmap Compose . au) . bu)
--  (aco . fmap (bco . fmap getCompose) . getCompose)

identityAdjunction = mkAdjlArA (\f -> Identity . f . Identity) (\f -> runIdentity . f . runIdentity)

curryAdjunction :: Adjunction ((,) t) ((->) t)
curryAdjunction = mkAdjlArA (\f a e -> f (e , a)) (\f (e , a) -> f a e)

adjM1 :: (Functor f, Functor r) =>
  Adjunction f r -> Adjunction (M1 i1 c1 f) (M1 i2 c2 r)
adjM1 a = mkAdjUnit (M1 . adjunctL a M1) (adjunctR a unM1 . unM1)

-- adj fusion (due to naturality properties of the adjuncts) --
-- R k · la f · h = la (k . f · L h)
-- k · ra g · L h = ra (R k · g · h) 
-- product fusion
-- (k1 × k2) · (f1 M f2) · h = (k1 · f1 · h) M (k2 · f2 · h)
pfLHS , pfRHS :: (x -> r) -> (y -> k) -> (b -> x) -> (b -> y) -> (a -> b) -> a -> (r , k)
pfLHS k1 k2 f1 f2 h = (k1 *** k2) . (f1 &&& f2) . h
pfRHS k1 k2 f1 f2 h = (k1 . f1 . h) &&& (k2 . f2 . h)
r (k1,k2)  = (k1 *** k2)

prodMorph (x , y) = (x , y)
-- L = Diag ; R = X
-- la = (Diag a -> b) -> a -> Prod b
-- a = s
-- r b = (x , y)
-- (l a -> b) -> a = (s -> x , s -> y)
la :: Arrow f => (f s x , f s y) -> f s (x , y)
la (f1 , f2) = f1 &&& f2
-- (l a -> b) -> a -> r b => (Diag a -> (b1,b2)) -> (a -> X (b1 , b2))
-- where Diag a = (a , a) and X (a , b) = a X b

data Prod (a :: (a1 , a2)) = Prod a1 a2
mkProd (a , b) = Prod a b
newtype Diag a = Diag (a , a)
mkDiag a = Diag (a , a)

--lla :: forall a (b :: (* , *)). (Diag a -> _) -> a -> Prod b
--lla :: (Diag a -> b) -> a -> Prod b
--lla d a = mkProd (d (Diag a))

--lla d a = mkProd (d (mkDiag a))

-- llla :: (Diag a -> _) -> a -> Prod b

-- pairs of arrows with same source BIJ with Arrows to a product
-- Product := x (f , g) = f x g
-- Diag := D a = (a , a)
-- (l a -> b) -> a -> r b
-- ((a , a) -> (b1,b2)) -> (a -> x (b1,b2))

-- L x = (x , x)
-- L _ = (s -> a , s -> b)
-- coUnit :: (l (r a)) -> a
-- coUnit = (outl , outr)

-- la : (l a -> b) -> a -> r b

-- pairs of arrows with the same source are 1-1 with arrows from a product
-- pairs of arrows with the same target are 1-1 with arrows from a coproduct

-- envReaderAdjunction = mkAdjUnit
--diagProdAdj = mkAdjUnit (\a -> _ (Pair a a)) _

sumProductAdj :: (Functor f, Functor g, Functor r1, Functor r2) =>
  Adjunction f r1 -> Adjunction g r2 -> Adjunction (Sum f g) (Product r1 r2)
sumProductAdj f g = mkAdjUnit (\a -> Pair (adjunctL f InL a) (adjunctL g InR a)) $ \case
  InL l -> adjunctR f (\(Pair x _) -> x) l
  InR r -> adjunctR g (\(Pair _ x) -> x) r

sumProdAdj :: (Functor f , Functor f' , Functor g , Functor g')
  => Adjunction f g -> Adjunction f' g' -> Adjunction (f :+: f') (g :*: g')
sumProdAdj adj1 adj2 = mkAdjUnit (\a -> (adjunctL adj1) L1 a :*: (adjunctL adj2) R1 a) (\case { L1 l -> (adjunctR adj1) (\(x :*: _) -> x) l ; R1 r -> (adjunctR adj2) (\(_ :*: x) -> x) r} )

-- Conjugate rule: c1 ~= c2
c1 :: (Functor d , Functor l , Functor r) =>
  Adjunction l r -> (l (d (r b)) -> b) -> (a -> d a) -> l a -> b
c1 adj a c = h where h = a . fmap{-L-} (fmap{-D-} (adjunctL adj h) . c) -- (3.9)
c2 adj a c = h where h = (adjunctR adj) (adjunctL adj a . fmap{-D-} (adjunctL adj h) . c)

hyloShift :: Functor d => (Identity (d (Identity b)) -> b) -> (a -> d a) -> Identity a -> b
hyloShift = c1 identityAdjunction

hAccu :: Functor d => ((p , d (p -> b)) -> b) -> (a -> d a) -> (p , a) -> b
hAccu = c1 curryAdjunction

--constParam :: Functor f => (f b -> b) -> (a -> f a) -> (a, p) -> b
--constParam a c = h where
--  h = a . fmap h . strength . (c *** identity)
--  strength :: Functor d => (d a , p) -> d (a , p)
--  strength (f , p) = fmap (,p) f
