# Irie
Array-oriented subtyping calculus of inductive constructions for high-performance distributed systems. [Basic language reference](languageDocumentation.md)

## Origin
Irie was created because there exists no pure functional language with first-class subtyping and an extreme emphasis on performance. Irie's philosophy is to focus exclusively on a simple but powerful core language capable of naturally expressing additional language features as native functions. That language is the subtyping calculus of constructions.

## Performance
Memory locality has become one of the key factors for performance, since cpu cache misses are very expensive (10 to 10000 times slower than a cpu instruction). Functional compilers take on the responsibility of managing all memory for the programmer, who has historically had good reason to distrust them. However, functional languages contain enough information that they could do a better job than even a C programmer using malloc can realistically maintain. For the next generation of functional compilers, a GC is no longer acceptable. Irie aims to compile all data driven functions with essentially a custom allocator, which emphasizes arena style blanket-frees to completely clean up the data-stack when data falls out of scope, as well as a tailored memory representation for recursive datas. In particular, for the familiar list type: `List a = Empty | Next a (List a)` the (List a) pointer can be made implicit by use of an array. In fact all recursive data structures can exploit one implicit pointer, or in the case of Peano arithmetic, directly become machine numbers. I note here that it is essential to optimize such data structures directly rather than ask users to use an opaque datatype (eg. `Vector a`), since that tends to be annoying and doesn't scale at all.

## Subtyping
Subtyping describes data flow explicitly and allows more accurate types. It can cleanly represent many desirable features (listed below). The key principle is that a subtyping relation (A <: B) implies the existence of a function (A -> B), which the compiler can automatically call. Some examples:
* Records with more fields are subtypes of those with less fields
* Sum types with less fields are subtypes of those with more
* Eg. Parametrized Ast's are often more accurately represented using Sumtype subtyping: instead of `LC a = Var a | Abs (LC a) [LC a] | etc`, define `LC = VarString String | Abs LC [LC] | etc` and use subtyping to substitute eg. `VarString String` with `VarInt Int`, when most of the AST and functions on it are reusable.
* Subtyping relations on algebraic data (records and sum types) are useful for quantitative type theory (including proof irrelevance).
* The dependent function space contains subtypes of the non-dependent function space
* Subtyping polymorphism is a sweet spot between parametric polymorphism and ad-hoc polymorphism, which enables us to say exactly what we mean.
* Bi-variant type parameters permit us to describe structures where insertable types are different to those that can be examined; e.g. input of any graphical component into a list after which we can use only their 'onClick' functions
* Subtyping increases the power of our types, and allow us to leverage automatic subtyping coercions to cleanly separate algorithms from optimisations
* Dependent types and subtyping gives types the power they need to guide an algorithm to its perfect implementation (which can become very complicated in the presence of GPUs or distributed systems)

## (semi)-automatic distributed computing (including GPU-offloading)
High level abstractions are necessary if we are to comfortably program using GPUs and distributed networks, since forking GPU kernels and sending programs over a network is far too tedious, error-prone and inflexible to do by hand. I propose to abstract implementation and optimisation details away from the terms and into the types.

# Compiler overview
* Source size: 4175 lines of Haskell
* Time to compile (dependencies not timed): 14.2sec (you tried your best GHC)

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
    - [x] Higher-rank inference (Impredicative polymorphism)
    - [ ] Type Checking of user supplied types
    - [x] Dependent Types
    - [ ] Normalization by evaluation
    - [x] Subtyping coercions
- LLVM Codegen:
    - [x] Lambda Calculus
    - [x] Algebraic data
    - [x] GMP bindings (only linked if used)
    - [ ] polymorphism
    - [ ] Memory management
    - [ ] GPU offloading
    - [ ] Distributed systems

# Discord server
https://discord.gg/3hYKngW
