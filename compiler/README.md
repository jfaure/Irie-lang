# Compiler Commentary

## Compiler pipeline
command line >> parse >> core >> STG >> llvm IR

1. Main parses the commandline and guides the compiler.
2. Parser : (Text -> PSyn) parses a single file; does not read import files.
3. Externs ; imported files are processed
4. Core is designed for type inference and checking
5. STG : (Core -> LLVM) The main difficulty is memory management
6. llvm IR is for processor specific optimizations and native code generation.

## General remarks
All algorithms used have worst case linear time complexity. name lookup is O(1) except on first encounter O(log n).
Mutable Vectors are used at every phase of compilation and are the choice data structure
Perfectionism is crucial; only the most direct solutions are used and I have a strong aversion for even miniscule increases in complexity.

## Parser
The parser handles names and scoping. Every argument and binding is assigned a unique (IName : Nat).

## Type inference / checking
This phase is heavily influenced by 'Algebraic subtyping' by Stephen Dolan, (but note we make no use of his type+scheme automata). Biunification is extended with QTT and dependent types (there is almost no friction between the 3).

## STG
trivial functions can be mapped more or less 1:1 to llvm. The difficulties are Memory management, polymorphism, subtype coercions (esp. extensible records), multithreading/distribution and implicit threading of free variables

### Memory management

### Record subtyping
This is key not only for records, but also sum type size classes in the allocator and unrolling of flat data. The issue is handling subsets of bigger structs transparently. Ideally the small struct is present wholly and intact within the bigger one, but there may be some unexpected fields in the middle, which amounts to some fields being bigger than expected.

### QTT
Main purpose is to improve runtime memory management
 * find the last read and free it there (this cannot always be statically determined, esp. if multithread)
 * if data is ours, we can use the memory directly
 * Let-bound / one-use functions are directly inlined (this has little effect on debugging thanks to llvm metadata)

## LLVM
conversion to llvm IR lacks a lot of the useful information present in Core and is thus only used for generating executables. LLVM is designed to optimize C/C++, and has little understanding of memory or our code in general, but can be relied on to optimize cpu primitives and leverage target-specific opportunities, as well as supporting numerous target architectures.
