# Compiler Commentary

## Compiler pipeline
command line >> parse >> core >> STG >> llvm IR

1. Main parses the commandline and guides the compiler.
2. Parser : (Text -> PSyn) parses a single file; does not read import files.
3. Externs : process imported files, unresolved names and mixfixes
4. Core is designed for type inference and checking
5. SSA : (Core -> SSA). Esp. memory management and subtyping coercions
6. llvm IR is for processor specific optimizations and native code generation.

## General remarks
* Perfectionism is crucial; Most files have been rewritten from scratch at least twice.
* Names are converted to Integers on sight, so lookup is O(1), except in the parser where (text->Int) lookup requires a O(log n) hashmap.
* Mutable Vectors (MVector s a) are the choice data structure most of the time

# Parser
The parser is designed to infaillably parse syntactically valid modules, handle Int names assignments and name shadowing. Issues of more complex name scoping, imported modules, external bindings and mixfixes are handled later.
The parser assigns every argument and binding a unique Int name and constructs a list of unknown names (forward and external references).

# Type inference / checking
This phase is heavily inspired by 'Algebraic subtyping' by Stephen Dolan, (minus the last chapter on automata). Biunification is extended with QTT and dependent types.

## Generalisation
We want polymorphic typing schemes to be instantiated with fresh variables on every use. We need to be careful to only generalise type variables that do not escape into enclosing scope. This is a good moment to simplify types by removing excessive type variables and tighten recursive types. Mutual functions need to be handled carefully.

# SSA Form; based on llvm, but (runtime)interpretable, linear and with untyped pointers
* Minor inconveniences are implicit threading of free variables
* Memory management
* polymorphism
* record subtyping
* Multithreading

#### Priorities
Since memory management corresponds to the problem of flattening tree structures (both datas and our call graph), it is generally impossible to avoid creating holes in memory, and we must at this stage assume there will be compromises. Thus it is important to set our priorities in order:
* The compiler can generate bookkeeping code in the program for the allocator (malloc implementations often work hard to find their headers, or perhaps worse, put them in front of every returned chunk)
* Don't track fragments individually: In FP we tend to generate many small pieces of data that 'belong' to a data structure (eg. List type). That data structure can usually manage it's fragments
* Identify potential for implicit pointers (Eg. List a = Z | Next a (List a)) must become a flat stack/array.
* No permanent damage: On return, functions cleanly recycle all memory they allocated
* Shared data may require extra bookkeeping; Unshared data shouldn't have to pay for this.

#### Allocator interface
mergeFrames : [Frames] -> Frame
shareFrame : Int -> Frame -> Frame
freeFrame : Frame -> ()

newFrag : Frame -> Size -> Frag
freeFrag : Frame -> Frag -> Size -> ()
dflist_mergeframes : [Frames] -> Frame
push : Frame -> Size -> Frag
pop  : Frame -> Size -> ()

### Record subtyping
This is key not only for records, but also sum type size classes in the allocator and unrolling of flat data. The issue is handling subsets of bigger structs transparently. Ideally the small struct is present wholly and intact within the bigger one, but there may be some unexpected fields in the middle, which amounts to some fields being bigger than expected.
