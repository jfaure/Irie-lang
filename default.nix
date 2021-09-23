with (import <nixos> {});

haskell.lib.buildStackProject {
  name = "irie";
  src = if lib.inNixShell then null else ./.;
  buildInputs = [ ghc llvm_9 ];
}
