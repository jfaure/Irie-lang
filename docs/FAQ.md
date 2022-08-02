Q: Is this similar to OOP (object oriented) Subtyping?
A: Absoluty not. The terminology is unfortunate: in subtyping literature, structural subtyping refers to a subtyping relation that relates only type constructors of the same arity. In OOP literature, structural subtying refers to implicitly formed relations from similar structures. Confusingly, this means structural typing requires non-structural subtyping. Irie's Subtyping always require conversion functions.

Q: Row polymorphism vs record subtyping?
A: Row polymorphism requires the use of higher kinded presence variables. It can express some types subtyping cannot, like a label which may or may not be present, but must be an Int if present. Conversely, subtyping can express some types row polymorphism cannot, like a function taking 2 records and returning a field f if either of the inputs did.

Q: Where did typeclasses go?
A: Typeclasses amount to slapping a Prolog language atop the core calculus, which is unnatural and complicates the entire compiler pipeline, while simultaneously admitting that the base language is somehow insufficient. Predictably, typeclasses don't extend organically and invite progressively weirder extensions and caveats (cf. haskell's Multiparam , Functional dependencies , flexiblecontexts , typesynonymInstances , overlappingInstances , orphan instances , lawless typeclasses , subtyping/inheritance of classes (eg. Monad < Applicative < Functor) etc..). Typeclasses are a hole out of which a language will never climb out of, which becomes especially painful since they complicate more useful extensions for type-level manipulations and first class polymorphism. Cynically, typeclasses may be called a failed experiment that is automatically replicated due to their ubiquity in haskell.

Q: Ad-hoc polymorphism?
Ostensibly typeclasses buy ad-hoc polymorphism. Irie supports this more cleanly using explicit records and subtyping to recover the convenience of automatic handling of overload dictionnaries. Irie also has functor modules which are frequently the best solution.

Q: Irie functions don't need type annotations?
A: Irie is exceptionally good at inferring types, so you should never need to provide a type signature. The only place type inference can fail is at function application, when incompatible arguments are given to a function.

Q: Only `let..in` no `where` ?
A: I don't like writing or reading code that mixes opposing styles. `let..in` nests better, is less awkward to format and the style of building up to a result is more natural then the addendum you get with `where`. I recommend using this layout:
```
square x = let
  result = x * x
  in result
```
