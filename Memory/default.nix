with (import <nixpkgs> {});
mkShell {
  buildInput = [ clang ];
}

