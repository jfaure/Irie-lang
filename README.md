# Nimzo
Array-oriented subtyping calculus of inductive constructions for high-performance distributed systems.

## Subtyping
Subtyping describes data flow explicitly and allows more accurate types, notably we can cleanly represent many desirable features, listed below. The key principle is that a subtyping relation (A <: B) is a proof of the existence of a function (A -> B), which the compiler can automatically call. Some points about subtyping:
* Records with more fields are subtypes of those with less fields
* Sum types with less fields are subtypes of those with more
* Subtyping relations on algebraic data (records and sum types) are useful for proof irrelevance, quantitative type theory, and so forth
* Effectful functions are supertypes of pure ones, which obviates the need for explicitly calling glue functions such as pure/return/etc.
* The dependent function space contains subtypes of the non-dependent function space
* Polymorphism is subtyping, eg: `Int <: forall a. a`
* Subtyping polymorphism is a sweet spot between parametric polymorphism and ad-hoc polymorphism, which enables us to say exactly what we mean.
* Bi-variant type parameters permit us to accurately describe structures where insertable types are different to those that can be examined; e.g. input of any graphical component into a list after which we can use only their 'onClick' functions
* Subtyping increases the power of our types, and allow us to leverage automatic subtyping coercions to cleanly separate algorithms from optimisations
* In conjunction with dependent types, the scope of possible optimisation opportunities becomes infinite, and subtyping can give types the power they need to guide an algorithm to its perfect implementation (which can become very complicated in the presence of GPUs or distributed systems)

## Calculus of inductive constructions
Dependent types have long served to write proofs which can be used to guarantee a program's correctness. In combination with subtyping, they introduce possibilities for powerful optimisations.

## Array-oriented
Much of the power of a machine is in its ability to handle vast quantities of organised data - most of which can be thought of as a tensor (a multi-dimensional array), including nested algebraic data structures. Thinking in terms of arrays makes it easier to coordinate operations and, for example, remove temporary structures via shortcut fusion. This is known to work very well for one-dimensional arrays, however, it notably fails to fuse both list arguments of zip - because zip is a rank 2 operation, outputting an array of shape [2 , n]. By generalising lists and nested algebraic data to tensor operations, we increase the scope of shortcut fusion.
  
## Distributed Performance
It has often been noted that higher level abstractions are necessary if we are to comfortably program using GPUs and distributed networks. It is necessary to abstract implementation and optimisation details away from the terms and into the types. Using subtyping, we can largely ignore the target system without sacrificing performance, as well as manipulate optimisations easily by annotating certain terms with detailed types.

### Roadmap
- Language:
    - [x] Lambda calculus
    - [x] MixFix operators
    - [x] Dependent Algebraic Data
    - [ ] GADT's (bivariant type parameters)
    - [x] Modules
    - [ ] As first class dependent records
- Type inference/checking:
    - [x] Lambda calculus
    - [x] Type Checking
    - [x] Dependent Types
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
    - [ ] Error reporting system

## Discord server
https://discord.gg/SXzVEB
