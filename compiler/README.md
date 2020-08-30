compiler

The compiler's plan is as follows:
command line >> parse >> core >> STG >> llvm IR

1. Main parses the commandline and guides the compiler accordingly
2. parse converts source files to parse tree
3. core is the preferred representation of a program, on which we perform type judgements and optimizations passes
4. STG implements the machinery to convert core to llvm IR (it's a special form of core)
5. llvm IR is the final program representation for processor-specific optimizations and native code generation. However it has lost type annotations and is somewhat more rigid than core, so the JIT keeps both.

Type checking
! Typejudge is only allowed to modify types,
  but can indirectly affect terms by leaving markers for core2stg; in particular class instances and PAps
