# Cery
Array-oriented Subtyping Calculus of inductive constructions for high-performance distributed systems

## Subtyping
Subtyping is a very promising concept:
 * records with more fields can be automatically coerced into records with less fields , which is useful for proof irrelevence and other simplifications
 * Terms are for algorithms , Types are for optimizations (using automatic conversions via subtyping)
 * The dependent function is a subtype of the non-dependent function
 * For automatic proofs, subtyping is more consistent than eg. instance arguments
 * Subtyping polymorphism, a sweet spot between parametric polymorphism and ad-hoc polymorphism
 * Other subtyping relations .. ?
 * In conjunction with dependent types, the scope of possible optimisation opportunities becomes infinite , and subtyping can give types the power they need to guide an algorithm to it's perfect implementation (which in the presence of GPUs or distributed systems can become very complex)

## Array-oriented
Part of the power of a computer is it's ability to handle vast quantities of organised data - much of which can be viewed as a tensor; a multidimensionnal array, including nested algebraic data. A key motivation for this is the removal of all intermediate structures via shortcut fusion (fold-build). Historically this has worked very well for one-dimensionnal arrays, however it notably fails to fuze both list arguments of zip - because zip is a rank 2 operation, outputting an array of shape [2 , n]. By generalising lists and nested algebraic data to tensor operations, we could vastly improve the scope of shortcut fusion. Working on the shapes of data regardless of the underlying mixture of types requires dependent types.

## Calculus of inductive constructions
Dependent types have a long history of serving to write proofs and otherwise guarantee program correctness. In combination with subtyping, they can also enable powerful optimisations

## Distributed
It has often been noted that higher level abstractions are necessary if we are to comfortably program using gpu's, or more generally, a distributed network. The solution is to program the algorithm as usual, and place all implementation and optimisation details in the types.

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
