# Arya Tset Seset
Array-oriented Subtyping Calculus of inductive constructions for high-performance distributed systems

## Subtyping
Subtyping is a very accurate way of representing many desirable features, since given two types and a subtyping relation (A <: B), the compiler can automatically call a function of type (A -> B).
 * polymorphism is subtyping: `Int <: ∀α.α`
 * records with more fields subtype those with less fields
 * Sum types with less fields can be automatically coerced into sum types with more
 * Subtyping relations on algebraic data (above) are useful for proof irrelevence and other simplifications
 * No need for strict positivity: subtyping allows bivariant type parameters (ie. things put into a data aren't the same as those taken out: eg. input graphical components into a list, take out only 'onClick' functions)
 * Subtyping describes data flow explicitly, and allows more precise types
 * Effectful functions supertype pure ones
 * Terms are for algorithms , Types are for optimizations (using automatic conversions via subtyping)
 * The dependent function is a subtype of the non-dependent function
 * Subtyping polymorphism is a sweet spot between parametric polymorphism and ad-hoc polymorphism
 * In conjunction with dependent types, the scope of possible optimisation opportunities becomes infinite , and subtyping can give types the power they need to guide an algorithm to it's perfect implementation (which in the presence of GPUs or distributed systems can be very far removed from it's simplest definition)

## Calculus of inductive constructions
Dependent types have a long history of serving to write proofs and otherwise guarantee program correctness. In combination with subtyping, they can also enable powerful optimisations, and become easier to use for general purpose programming.

## Array-oriented
Part of the power of a computer is it's ability to handle vast quantities of organised data - most of which can be thought of as a tensor; a multidimensionnal array, including nested algebraic data. This representation is motivated by the ability to remove all intermediate structures via shortcut fusion (fold-build). This is known to work very well for one-dimensionnal arrays, however it notably fails to fuze both list arguments of zip - because zip is a rank 2 operation, outputting an array of shape [2 , n]. By generalising lists and nested algebraic data to tensor operations, we vastly improve the scope of shortcut fusion. Working on the shapes of data regardless of the underlying mixture of types requires dependent types.

## Distributed
It has often been noted that higher level abstractions are necessary if we are to comfortably program using gpu's, or more generally, a distributed network. The solution is abstract implementation and optimisation details away from the terms and into the types. Using subtyping, we can largely ignore the target system without sacrificing performance.

### Roadmap
- Language:
    - [x] MixFix operators
    - [x] Lambda calculus
    - [x] Dependent Algebraic Data
    - [ ] GADT's (bivariant type parameters)
    - [x] Module System
        - [ ] As first class dependent records
- Type inference/checking:
    - [x] Lambda calculus
    - [x] Type Checking
    - [ ] Dependent functions
    - [ ] Dependent Records
    - [ ] Higher-rank inference (Impredicative polymorphism)
- LLVM Codegen:
    - [x] Lambda Calculus
    - [x] Algebraic data
    - [ ] polymorphism
    - [ ] Subtype coercions
    - [ ] Stack-based lifetime oriented Memory model
    - [ ] GPU offloading
    - [ ] Distributed systems
- Environment:
    - [ ] Precompiled modules
    - [ ] Language server
