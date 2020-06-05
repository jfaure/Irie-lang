# Arya
Array-oriented Calculus of inductive constructions for high-performance distributed systems

* Impredicative type inference
* LLVM backend
* multi-dimensionnal fold-build
* effect style (rather than monadic)

## Array-oriented
Everything can be viewed as a tensor; a multidimensionnal array, including nested algebraic data. A key motivation for this is the removal of all intermediate structures via shortcut fusion (fold-build). Historically this has worked very well for one-dimensionnal arrays, however it notably fails to fuze both list arguments of zip - that's because zip is a rank 2 operation, and can be thought of as outputting a 2xn array. Arya aims to completely remove all intermediate structures by generalising lists and nested algebraic data to tensor operations

## Calculus of inductive constructions
Dependent types are most often used to guarantee program correctness. However, I am more interested in optimisation opportunities: Terms can depend on types via polymorphism - this is key to abstracting all optimisation details away from the actual program algorithm, which should live in isolation at the term level. In order to give our types the power they need to guide an algorithm to it's perfect implementation (which in the presence of distributed systems or GPU programming may be very complex), we also need dependent types, ie. the ability to construct types from arbitrary terms.

## Distributed
It has often been noted that higher level abstractions are necessary if we are to comfortably program using gpu's, or more generally, a distributed network. The solution is to program just the algorithm at the term-level, and place all implementation detailsin the types, making heavy use of polymorphism and type matching.

### Roadmap
- Top-Level:
    - [x] subtyping
    - [x] records
    - [x] sum-types
    - [ ] Dependent types
    - [ ] GADT's 
    - [ ] Distributed systems
- Parser:
    - [x] Lambda calculus
    - [x] MixFix operators
    - [x] Module System
        - [x] Modules as first class dependent records
- Type inference:
    - [x] Lambda calculus
    - [x] Type Checking
    - [ ] Dependent types
    - [ ] Higher-rank inference (Impredicative polymorphism)
- LLVM Codegen:
    - [x] Lambda Calculus
    - [ ] polymorphism
    - [ ] Subtype coercions
    - [ ] Stack-based lifetime oriented Memory model
