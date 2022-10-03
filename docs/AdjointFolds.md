universal property ⇒ Fold = unique solution of its defining equation

initial algebras dualise to final coalgebras ; folds dualise to unfolds

wrap arg of fold / result of unfold in functor application

mutu adjunction captures obs that pair of arrow to same codomain can be single arrow from coproduct of the domains

transform nested recursion into mutual recursion

folds of higher-order initial algebras are natural transformations (live in functor category)

sumPerfectTree ; need to view type application as a functor

Table of adjunctions: pg 30 "Adjoint folds and unfolds"

fuse left adjoint with initial algebra to form another intial algebra
universal property = fold is unique solution to defining equation

Termination is an operational notion, it's translation to denotational setting depends on underlying category

L has a right adjoint iff the left kan extension Lan(L) Id exists and is preserved by L

using base functor fusion shift application of `map f` into adjoint fold:
⦇cat⦈L . L (map f) = ⦇λcat.'cat' cat . L (map f)⦈L

Fusion: Let h : D(B, A), then
  [(Φ)]R · h = [(Ψ)]R ⇐= ∀x . Φ x · h = Ψ (x · h).
Conjugate fusion: Let τ : R ˙→ R ′ , then
  τ · [(Ψ)]R = [(Ψ ′)]R ′ ⇐= ∀x . τ · Ψ x = Ψ ′ (τ · x).
General fusion: Let α : ∀X : C . D(A, R X) → D ′ (A ′ , R ′ X), then
  α [(Ψ)]R = [(Ψ ′)]R ′ ⇐= α · Ψ = Ψ ′ · α.
Base functor fusion: Let α : G ˙→ F, then
  R (να) · [(Ψ)]R = [(λ x . R α · Ψ x)]R , where να = [(α (νG) · out)].

show List ◦ Maybe ∼= Maybes
underlying adjunction is pre-composition PreMaybe ⊣ RanMaybe
× distributes over + and 1 × B ∼= B

µF and νF are not compatible ⇒ we cannot combine folds - can work in category where they coincide or restrict unfolds to coalgebras that produce values in µf. An attractive way to achieve the latter is using hylomorphisms based on recursive coalgebras as a structured recursion scheme.


-----------------------------
-- Conjugate Hylomorphisms --
-----------------------------

Rolling rule: base functor shaping recursion is composed from 2 other functors & allows swapping
Conjugate rule: shunt functors between producer and consumer parts of the hylo

apomorphism allows coalgebra to stop the recursion early

F-homomorphism between algebras (a,A) (b,B) is an arrow h:A → B:C such that h . a = b . F h

(A + _) can be used to model tail recursion
h = (id ▽ id) . (A + h) . c <==> h = (id ▽ h) . c
id ▽ id : A + A → A is the codiagonal.

! hylomorphisms do not compose; a hylo composes with algebra and co-algebra homomorphisms

assemble recursive coalgebras so by definition hylos have unique solutions
parametrically recursive coalgebras (original input also passed to algebra)
