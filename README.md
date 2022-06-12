# Irie
Subtyping calculus of inductive constructions for high-performance (and eventually distributed) systems.

![logo](https://cdn.discordapp.com/attachments/631043990879338496/756673093497520138/logo.png)
## [Tutorial (TODO)](tutorial.md)
## [Language documentation (WIP)](languageDocumentation.md)
## [Compiler Internals](compiler/README.md)

## Origin
Irie is the first pure functional language with first-class subtyping and an extreme emphasis on performance. The philosophy is to focus on a simple but powerful core language capable of naturally expressing additional desirable features: The subtyping calculus of constructions.

## Subtyping
Subtyping describes data flow explicitly and allows more accurate types. Formally, it is enough that a function of type `A -> B` exists for a subtyping relation `A <: B` to be permissible, in which case the compiler will automatically call the function where needed. Subtyping can cleanly (as opposed to an adhoc approach that won't scale) represent many desirable features (listed below). In practice it is both convenient and a mechanism to give types some control over terms. Types with influence over terms can guide a program to its optimal implementation (which in the presence of GPUs or distributed systems may be very complicated), without requiring programmers to pollute their algorithms with esentially irrelevant details. The question of what (if any) custom subtyping relations libraries should add is still open. In any event, "excessive" subtyping relations cannot violate typing guarantees.

Subtyping examples:
* Integer bitwidths `int32 <: int64` C has this, calling it integer promotion
* Records with excess fields  `{x : Int , y : Int} <: {x : Int}`. Convenient and informs the compiler that it can release memory and resources tied in the dropped field 'y'
* Sum-types with fewer labels `[circle : Int] <: [circle : Int | square : Int]`
* Parameterized data (including GADTs): instead of `LC a = Var a | Abs (LC a) [LC a] | etc`, define `LC = VarString String | Abs LC [LC] | etc` then elsewhere substitute `VarString String` with eg. `VarInt Int`, when via subtyping the rest of the AST and many functions on it are reusable.
* Subtyping relations on algebraic data (records and sum types) are useful for quantitative type theory (including proof irrelevance).
* The dependent function space contains subtypes of the non-dependent function space
* Subtyping polymorphism is the sweet spot between parametric polymorphism and ad-hoc polymorphism, being both simple and equally powerful
* Bi-variant type parameters accurately describe structures where insertable types are different to extractable types; e.g. input of any graphical component into a list after which we can use only their 'onClick' functions
* Extra subtyping relations can enable custom optimisations

## Performance
### Fusion
Cata-Build and stream fusion are techniques for automatically eliminating many intermediate datastructures. Catamorphisms can fuse with anything, however this direction of travel cannot fuse zips or other functions of multiple datas. Stream fusion is more powerful, but more difficult to implement since it depends on co-recursion and general compiler optimisations and in particular specialisation of partial applications. Both of these fusion framewords traditionally require functions to be written in a restricted form, but this form can often be automatically derived from general recursive definitions. See "Stream Fusion: From Lists to Streams to Nothing at All" and "Warm Fusion: Deriving Build-Catas from Recursive definitions"

### Memory
Memory locality has become a key factor for performance (cpu cache misses can be 10 to 10000+ times slower than a cpu instruction). Functional compilers take on the responsibility of managing all memory for the programmer, who has historically had good reason to distrust them. However they have enough information to do a better job than even a C programmer using malloc could realistically maintain. For the next generation of functional compilers, both a GC and excessive reference counting are no longer acceptable. Irie aims to compile all data driven functions with essentially a custom allocator, which emphasizes arena style blanket-frees to completely clean up the data-stack when data falls out of scope, as well as a tailored memory representation for recursive datas. For example, the familiar list type: `List a = Empty | Next a (List a)` the (List a) pointer can be made implicit by use of an array. Indeed all recursive data structures can exploit one implicit pointer, or in the case of Peano arithmetic, directly become machine numbers. I note here that in the interests of scalability it is essential to optimize such data structures directly rather than force users to use an opaque datatype (eg. `Vector a`).

## (semi)-automatic distributed computing (including GPU-offloading)
High level abstractions are necessary if we are to comfortably program using GPUs and distributed networks, since deciding when its appropriate and then forking GPU kernels or sending programs over a network is far too tedious, error-prone and inflexible to do manually, I believe the way forwards is to abstract implementation and optimisation details away from the terms and into our flexible subtyping lattice of types.

## Usage `$ irie --help`
```
Irie compiler/interpreter

Usage: [-p|--print ARG] [-j|--jit] [-d|--debug] [-O ARG]
       [-n|--no-prelude] [-o ARG] [FILE]
  Compiler and Interpreter for the Irie language, a subtyping CoC for system
  level programming.

Available options:
  -h,--help                Show this help text
  -p,--print ARG           print compiler pass(es separated by ',') : [args |
                           source | parseTree | core | llvm-hs | llvm-cpp]
  -j,--jit                 Execute program in jit
  -d,--debug               Print information with maximum verbosity
  -O ARG                   Optimization level [0..3]
  -n,--no-prelude          don't import prelude implicitly
  -o ARG                   Write llvm output to file
```

# Status
## Source size: ~5000 lines of Haskell

## Roadmap
- Language:
    - [x] Lambda calculus
    - [x] MixFix operators
    - [x] Dependent Algebraic Data
    - [ ] GADT's (bivariant type parameters)
    - [x] Modules
    - [ ] As first class dependent records
- Type inference/checking:
    - [x] Lambda calculus
    - [x] Subtyping coercions
    - [x] Type Checking of user supplied types
    - [ ] Higher-rank inference (Impredicative polymorphism)
    - [x] Dependent Types
    - [ ] Normalization of dependent types
- Procedural IR
    - [x] Lambda Calculus
    - [x] Algebraic data
    - [ ] polymorphism
    - [ ] Memory management
    - [ ] GPU offloading
    - [ ] Distributed systems
    - [x] C backend
    - [x] X86_64 backend

## [References](references)

# Discord server
https://discord.gg/3hYKngW
