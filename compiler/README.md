# Compiler Commentary

## Compiler pipeline
command line >> parse >> core >> STG >> llvm IR

1. Main parses the commandline and guides the compiler.
2. Parser : (Text -> PSyn) parses a single file; does not read import files.
3. Externs : process imported files, unresolved names and mixfixes
4. Core is designed for type inference and checking

## General remarks
* Names are converted to Ints on sight, so after the O(log n) hashmap lookup at parse, all indexing is O(1)
* Mutable Vectors (MVector s a) are the necessary data structure most of the time

# Parser
The parser is designed to infaillably parse syntactically valid modules, handle Int name assignments and generate the main module bindings vector. Issues of name scoping, imported modules, external bindings and mixfixes are handled later.

# Mixfixes
Mixfixes aren't all in scope at parse-time, and we go even further and infer all arguments to find their scope and QNames before resolving mixfixes. Mixfixes are solved using megaparsec again, this time on a list of CoreSyn.Expr

# Core
* bindings vector needs a topological sort so dependencies , dependents and cycles are clearly marked

# Type inference / checking
This phase is based on 'Algebraic subtyping' by Stephen Dolan

## Generalisation
We want polymorphic typing schemes to be instantiated with fresh variables on every use. We need to be careful to only generalise type variables that do not escape into enclosing scope. This is the time to simplify types by removing excessive type variables and tighten our equi-recursive types. Mutual functions need to be handled carefully.

# Memory Priorities
Since memory management corresponds to the problem of flattening tree structures, it is generally impossible to avoid creating holes in memory. Thus we immediately prepare for compromise by setting our priorities in order:
* The compiler may generate bookkeeping code & data
* Data structures should manage their own fragments
* Identify potential for implicit pointers (Eg. List a = Z | Next a (List a)) must become a flat stack/array.
* No permanent damage: On return, functions cleanly recycle all memory they allocated
* Shared data may require extra expense; Unshared data shouldn't have to pay for this.

### Record subtyping
This is key not only for records, but also sum type size classes in the allocator and unrolling of flat data. The issue is handling subsets of bigger structs transparently. Ideally the small struct is present wholly and intact within the bigger one, but there may be some unexpected fields in the middle, which amounts to some fields being bigger than expected.
