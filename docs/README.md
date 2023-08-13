# Irie
Fused subtyping calculus of constructions

![logo](https://cdn.discordapp.com/attachments/631043990879338496/756673093497520138/logo.png)
## [Intro (pagedown)](#origin)
## [Business Value (Non-technical overview)](BusinessValue.md)
## [FAQ](FAQ.md)
## [Tutorial (WIP)](tutorial.md)
## [Language documentation (WIP)](languageDocumentation.md)
## [Compiler Internals](../compiler/README.md)
## [References](references)

## Origin
Irie is the first pure functional language with first-class subtyping and an extreme emphasis on performance. The philosophy is to focus on a simple but powerful core language capable of naturally expressing additional desirable features: The subtyping calculus of constructions.
"The purpose of abstraction is not to be vague, but to create a new semantic level in which one can be absolutely precise" - E.W.Dijkstra

## Subtyping
Subtyping describes data flow explicitly and allows more accurate types. Formally, it is enough that a function of type `A -> B` exists for a subtyping relation `A <: B` to be _permissible_, in which case the compiler will automatically call the function where needed. Subtyping can cleanly (as opposed to an adhoc approach that won't scale) represent many desirable features (listed below). In practice it is both convenient and a mechanism to give types some control over terms; Types may guide a program to its optimal implementation (which in the presence of SIMD , GPUs or distributed systems may be very complicated), without requiring programmers to pollute their algorithms with esentially irrelevant details. The question of what (if any) custom subtyping relations libraries should add is still open. In any event, "excessive" subtyping relations cannot violate typing guarantees.

Subtyping examples:
* Integer bitwidths `int32 <: int64` C has this, calling it integer promotion
* Records with excess fields  `{x : Int , y : Int} <: {x : Int}`. Convenient and informs the compiler that it can release memory and resources tied in the dropped field 'y'
* Sum-types with fewer labels, eg: Nonempty lists subtype lists `µx.[One a | Cons a x] <: μx.[None | One a | Cons a x]`
* Lifetimes are ordered by a subtyping relation `a: b` (a outlives b), if the lifetime a contains all of b. References to references `&a &b T` are valid if and only if the reference lifetime does not outlive its contents.
* Parameterized data (including GADTs): instead of `LC a = Var a | Abs (LC a) [LC a] | etc`, define `LC = VarString String | Abs LC [LC] | etc` then elsewhere substitute `VarString String` with eg. `VarInt Int`, when via subtyping the rest of the AST and many functions on it are reusable.
* Subtyping relations on algebraic data (records and sum types) are useful for quantitative type theory (including proof irrelevance).
* The dependent function space contains subtypes of the non-dependent function space
* Subtyping polymorphism is the sweet spot between parametric polymorphism and ad-hoc polymorphism, being both simple and equally powerful
* Bi-variant type parameters accurately describe structures where insertable types are different to extractable types; e.g. input of any graphical component into a list after which we can use only their 'onClick' functions
* Extra subtyping relations can enable custom optimisations

## Performance
### Limitations of C (and LLVM)
The initial plan was to emit C directly. Several annoyances with C later and irie now emits asm directly:
* Functions with multiple entrypoints: particularly important for specialisations of cases
* builtin unfoldStack : (b -> Maybe (Char , b)) -> b -> CString

C won't allow this since it reserves the right to spill registers to the stack, even for cases like this where it is guaranteed not to happen
* Calling conventions. stdcall/ccall and also fastcall/regcall don't make nearly as much use of registers as a functional language would like. SIMD registers and the vpshufb instruction are particularly important for records and record subtyping.
* Dynamic linking is messy and slow, requiring actual textual function names inside binaries with no oversight. It also doesn't mesh well with JIT.
* Dependent types require a JIT, and writing directly to mem then calling that is orders of magnitudes faster than emitting C/LLVM is very slow and not too useful besides suport for many obscure CPU architectures and some peephole optimisations.

### SIMD
The operation `x * y : Float` can be made to run almost 10 times faster using SIMD: AVX can perform 8 floating point instructions at once (similarly 32 bytewise, four 64-bit instructions). This happens using SSE/AVX instruction sets and wide registers within the CPU. AVX512 doubles this again and will become standard with DDR5 RAM machines that bottleneck less on memory. Vector instructions are far too powerful to ignore but also too painful to write manually all the time: They can be emitted automatically following fusion and subtyping.

### Fusion: cata-fusion (leaves -> root) , ana-fusion (root -> leaves)
Cata-fusion and ana-fusion techniques aim to automatically eliminate intermediate datastructures. Catamorphisms can fuse with any one (but only one) input, since they amount to replacing all constructors with the provided function, eg. the list catamorphism foldr `foldr _+_ 0` means `replace Cons with _+_ and Nil with 0 everywhere in the list`. This approach can only fuse one input list (Famously failing to fuse both args to `zip`). Ana fusion is more powerful, capable of fusing multiple input streams, but more complicated since its success depends on co-recursion and general compiler optimisations; particularly the tricky specialisation of partial applications. The formalism for both fusion frameworks traditionally requires (library) functions to be written in a restricted form. See "Stream Fusion: From Lists to streams to Nothing at All" and "Warm Fusion: Deriving Build-Catas from Recursive definitions"

### Memory
Memory locality has become a key factor for performance, since CPU cache misses can be 10 to 100+ times slower than a cpu instructions. Functional compilers take on the responsibility of managing all memory for the programmer, who has historically had good reason to distrust them, yet FP compilers have more than enough information to do a better job than even a C programmer using malloc can realistically maintain. Irie relies on ana-fusion and β-optimal techniques to allocate data linearly and differently for recursive functor. Duplications follow β-optimal theory by lazily cloning recursive structures layer by layer. The familiar list type provides a simple yet crucial example: `IntList = Empty | Next Int IntList` , aka `μx.[Empty | Next Int x]` the IntList pointer can be made implicit if we flatten the structure to an array. All recursive data structures can exploit at least one implicit pointer. Additionally tree-structures can be decomposed into a pair of an NFA(non-deterministic finite automaton) and array of auxilary data. This format is more suitable for free unzipping, free label filtering and SIMD. Furthermore recursive non-container datas (Peano arithmetic) is modellable by machine numbers, and raw labels by BitSets. In the interest of scalability it is essential to optimize arbitrary structures directly rather than force users to use magic opaque datatypes (eg. `Vector a`).

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
  -o ARG                   Write output to file
```

# Discord server
https://discord.gg/3hYKngW
