with (import <nixos-unstable> {});

haskell.lib.buildStackProject {
  name = "nimzo";
  src = ./.;
  buildInputs = [ ghc llvm_9 ];
}
