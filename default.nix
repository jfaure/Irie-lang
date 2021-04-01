with (import <nixos> {});

haskell.lib.buildStackProject {
  name = "nimzo";
  src = if lib.inNixShell then null else ./.;
  buildInputs = [ ghc llvm_9 ];
}
