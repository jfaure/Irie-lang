# Monotype environments (typing schemes)
2 environments have a greatest lower bound: d1 n d2, where (d1 n d2) (x) = d1(x) n d2(x)
interpret d1(x) = T for x not present in d1
! subsumption (on typing schemes) allows instantiation of type variables

# Generalization
suppose `e = let x = e1 in e2`. e1 must be typeable and have principal ty [D1-]t1+ under Pi
the most general choice is to insert x into Pi with principal type of e1
ie. x depends on lambda-bound vars, so those are moved into Pi (as monotype environments)

Generalisation: we want polymorphic typing schemes to be instantiated with fresh variables on every use
  * lift all dominated irreducible THVars and THArgs to debruijn Pi bindings
  * generalize at Abs (mutual functions together)
  * only modify dominated type variables "Dominion" data (messing with the environment is obviously unsound)
Simplification is incidentally conveniently handled now:
  * remove polar variables (those that appear only positively or only negatively) `a & int -> int`
  * unify inseparable positive variables (co-occurence `a&b -> a|b` and indistinguishable variables `a->b->a|b`)
  * unify variables that contain the same upper and lower bound (a<:t and t<:a)`a&int->a|int`
  * minimize recursive types that may have been unrolled during biunification

# Note. Rank-n polymorphism
A constraint a <= t- gives a an upper bound ;
which only affects a when used as an upper bound (negative position)
The only exception is when inferring higher-rank polymorphism,
since a- and a+ must have the same polymorphic rank

# BiSubstitution
find substitution solving constraints of the form t+ <= t-
Atomic: (join/meet a type to the var)
a  <= t- solved by [m- b = a n [b/a-]t- /a-] 
t+ <= a  solved by [m+ b = a u [b/a+]t+ /a+] 
a  <= c  solved by [m- b = a n [b/a-]c  /a-] -- (or equivalently,  [a u b /b+])
SubConstraints, eg: (t1- -> t1+ <= t2+ -> t2-) = {t2+ <= t1- , t+ <= t2-}


# Recursive Types
Recursive types are guarded and covariant
(ie. `Ma. (a->bool)->a` ok, but not `Ma. a->Bool`)
however,
FA t+ , EX t+a and tg+ where ta+ is Bottom or a,
ta+ is guarded in tg+ and t+ = ta+ U tg+
ie. guarded can be weakened to a least pre-fixed point operator mu+:
`mu+ a. t+ = mu a. tg+`
guardedness is only required to coincide mu+ and mu-
covariance excludes `mu a. a->a` ?
: look at 2 types: t1=t2->t1 and t2=t1->t2
can introduce mus by covariances , and
by substitution: `t1=mu a. (mu b. t1->b) -> a`
mu is monotone, so t1 and t2 are still covariant;
t1 = mu a'. mu a. (mu b. a' -> b) -> a
t1 = mu a. (mu b. a->b) -> a
guardedness is crucial here, to introduce mu in t2->t1
otherwise mu+ and mu- wouldn't be the same

non-regular recursion ?
eg. isorecursive non-regular: add opaque roll/unroll primitives

The lambda-bound types here are flexible ie. subsumption can occur before beta-reduction. This can be weakened by instantiation to a (monomorphically abstracted) typing scheme.
We have to unconditionally trust annotations so far as the rank of polymorphism, since that cannot be inferred (cannot insert type abstractions) 
