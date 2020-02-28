with (import <nixos-unstable> {});

haskell.lib.buildStackProject {
  name = "arya";
  src = ./.;
  buildInputs = [ ghc llvm_9 ];
}
