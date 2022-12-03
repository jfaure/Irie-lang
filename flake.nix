{
  description = "irie";
  inputs = {
    nixpkgs-upstream.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    haskell-nix.url = "github:input-output-hk/haskell.nix";
    nixpkgs.follows = "haskell-nix/nixpkgs-unstable";
    haskell-nix-extra-hackage = {
      url = "github:mlabs-haskell/haskell-nix-extra-hackage";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.haskell-nix.follows = "haskell-nix";
    };
    connections   = { url = "github:cmk/connections"; flake = false; };
    coapplicative = { url = "github:cmk/coapplicative"; flake = false; };
  };
  outputs = inputs@{ self, nixpkgs, nixpkgs-upstream, haskell-nix, haskell-nix-extra-hackage, ... }:
  let
  plainNixpkgsFor = system: import nixpkgs-upstream { inherit system; };
  compiler-nix-name = "ghc925";
  hackagesFor = system: haskell-nix-extra-hackage.mkHackagesFor system compiler-nix-name
    [ "${inputs.connections}"
      "${inputs.coapplicative}"
    ];
  supportedSystems = [ "x86_64-linux" ];
# perSystem = nixpkgs.lib.genAttrs supportedSystems;
  perSystem = nixpkgs-upstream.lib.genAttrs supportedSystems;
  nixpkgsFor = system: import nixpkgs {
    inherit system;
    inherit (haskell-nix) config;
    overlays = [ haskell-nix.overlay ];
    };
  cabalProjectLocal = ''
  allow-newer: profunctor-optics:connections
  allow-newer: *:connections
  allow-newer: *:newtype-generics
  constraints: connections >= 0.3.2
  '';
# allow-newer: newtype-generics:base
  nixpkgsFor' = system: import nixpkgs { inherit system; };
  projectFor = system: let
    hackages = hackagesFor system;
    pkgs = nixpkgsFor system;
    plainPkgs = plainNixpkgsFor system;
    in (nixpkgsFor system).haskell-nix.cabalProject' {
      inherit compiler-nix-name cabalProjectLocal;
      inherit (hackages) extra-hackages extra-hackage-tarballs;
      src = ./.;
      index-state = "2022-08-05T00:00:00Z";
      modules = [{ packages = { }; }];
      shell = {
#          inherit (preCommitCheckFor system) shellHook;
        tools = { cabal = {}; };
        withHoogle = false;
        exactDeps  = true;
        nativeBuildInputs = [];
        };
      };
  formatCheckFor = system: let pkgs = nixpkgsFor system; in
    pkgs.runCommand "format-check" {
        nativeBuildInputs = [ self.devShell.${system}.nativeBuildInputs ];
      } ''
      cd ${self}
      export LC_CTYPE=C.UTF-8 LC_ALL=C.UTF-8 LANG=C.UTF-8 IN_NIX_SHELL='pure'
      make format_check cabalfmt_check nixpkgsfmt_check lint
      mkdir $out
    '';
  in {
  inherit plainNixpkgsFor hackagesFor cabalProjectLocal;
  project  = perSystem projectFor;
  flake    = perSystem (system: (projectFor system).flake {});
  packages = perSystem (system: self.flake.${system}.packages);
  devShell = perSystem (system: self.flake.${system}.devShell);
  apps = perSystem (system: self.flake.${system}.apps // {default = self.flake.${system}.apps."irie:exe:irie-exe";});
  };
}
