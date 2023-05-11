Q: OOP (object oriented) Inheritance vs Subtyping?

A: Subtyping: B subtypes A if it contains all of A's interface and possibly more. Per Liskov's substitution principle, any context where A is needed, B works also. Inheritance means B specialises A to a particular use (perhaps by overriding)

Q: Structural subtyping ?

A: The terminology is unfortunate: in subtyping literature, structural subtyping refers to a subtyping relation that relates only type constructors of the same arity. In OOP literature, structural subtying refers to implicitly formed relations from similar structures. Confusingly, this means structural typing requires non-structural subtyping. Irie's Subtyping always require conversion functions.

Q: What are ⊤ and ⊥ (top and bottom)?

A: ⊥ = ∀α.α can be used at any type, but cannot be constructed. ⊤ = ∃α.α can be constructed from any type , but cannot be used

Q: Row polymorphism vs record subtyping?

A: Row polymorphism requires the use of higher kinded presence variables. It can express some types subtyping cannot, like a label which may or may not be present, but must be an Int if present. Conversely, subtyping can express some types row polymorphism cannot, like a function taking 2 records and returning a field f if either of the inputs did.

Q: Where did typeclasses go?

A: Typeclasses amount to slapping a Prolog language atop the core calculus, which is unnatural and complicates the entire compiler pipeline, while simultaneously admitting that the base language is somehow insufficient. Predictably, typeclasses don't extend organically and invite progressively weirder extensions and caveats (cf. haskell's Multiparam , Functional dependencies , flexiblecontexts , typesynonymInstances , overlappingInstances , orphan instances , lawless typeclasses , subtyping/inheritance of classes (eg. Monad < Applicative < Functor) etc..). Typeclasses are a hole out of which a language will never climb out of, which becomes especially painful since they complicate more useful extensions for type-level manipulations and first class polymorphism. Cynically, typeclasses may be called a failed experiment that is automatically replicated due to their ubiquity in haskell.

Q: Ad-hoc polymorphism?
A: The ability for the same binding to behave differently depending on the type of arguments can be convenient: the most compelling example being arithmetic on numeric types. 'type-case' is theoretically problematic however. The solution here is using explicit labels to denote alternative types and subtyping to recover the convenience and implicit nature of typeclasses. Irie also has functor modules which are usually the best solution.

Q: Unicode syntax?

A: There is little builtin syntax so only `\` = `λ` , `\case` = `λcase` and `=>` = `⇒` have a unicode alternative builtin to Irie's parser. Of course the prelude and libraries export unicode alternatives for many standard functions. To input unicode, most editors support digraphs, so eg. in vim Ctr-k (see :digraphs) enables digraph input, then l* = λ , => = ⇒ , FA = ∀ and so on. It is also possible to setup some macros in case you want typing => to automatically insert ⇒.

Q: Irie functions don't need type annotations?

A: You should never need to provide a type signature. The only place type inference can fail is at function application, when incompatible arguments are given to a function.

Q: Only `let..in` no `where` ?

A: `where` may be added. for now I don't like code that mixes opposing styles. `let..in` nests better, is less awkward to format and the style of building up to a result is usually more natural then the addendum you get with `where`.
