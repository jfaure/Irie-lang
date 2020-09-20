# Nimzo
Array-oriented subtyping calculus of inductive constructions for high-performance distributed systems. [Basic language reference](languageDocumentation.md)

## Calculus of inductive constructions
Dependent types have long served to write proofs which can be used to guarantee a program's correctness. In combination with subtyping, they introduce possibilities for powerful optimisations.

## Array-oriented
Much of the power of a machine is in its ability to process vast quantities of organised data. Manipulating information with aggregate operations and generally thinking in terms of arrays corresponds more closely to our algorithms. The compiler also finds aggregate operations easier to coordinate operations and optimize (esp. by removal of temporary structures via shortcut fusion). Tensors are multi-dimensional arrays and correspond to many types of organised data.

## Distributed computing
High level abstractions are necessary if we are to comfortably program using GPUs and distributed networks, since forking GPU kernels and sending programs over a network is far too tedious, error-prone and inflexible to do by hand. I propose to abstract implementation and optimisation details away from the terms and into the types.

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

# Roadmap
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

# Discord server
https://discord.gg/3hYKngW
