{
  description = "irie compiler";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    horizon-gen-nix.url = "git+https://gitlab.homotopic.tech/horizon/horizon-gen-nix?ref=refs/tags/0.6.1";
    horizon-platform.url = "git+https://gitlab.homotopic.tech/horizon/horizon-platform";
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
  };

  outputs =
    inputs@
    { self
    , flake-utils
    , horizon-gen-nix
    , horizon-platform
    , nixpkgs
    , ...
    }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
    let pkgs = import nixpkgs { inherit system; }; in with pkgs.haskell.lib.compose;
    let
      myOverlay = pkgs.lib.composeManyExtensions [
#       (import ./overlay.nix { inherit pkgs; })
        (final: prev: { irie = final.callCabal2nix "irie" ./. { }; })
      ];
      legacyPackages = horizon-platform.legacyPackages.${system}.extend myOverlay;
    in {
      apps = {
        horizon-gen-nix = horizon-gen-nix.apps.${system}.horizon-gen-nix;
      };
      devShells.default = legacyPackages.irie.env.overrideAttrs (attrs: {
        buildInputs = with pkgs; attrs.buildInputs ++ [
          legacyPackages.cabal-install
        ];
      });
      packages.default = legacyPackages.irie;
    });
}
