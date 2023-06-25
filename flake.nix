{
  description = "irie compiler";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    horizon-platform.url = "git+https://gitlab.horizon-haskell.net/package-sets/horizon-platform";
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
  };

  outputs =
    inputs@
    { self
    , flake-utils
    , horizon-platform
    , nixpkgs
    , ...
    }:
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
    let pkgs = import nixpkgs { inherit system; }; in with pkgs.haskell.lib.compose;
    let
      myOverlay = pkgs.lib.composeManyExtensions [
#       (import ./overlay.nix { inherit pkgs; })
        (final: prev: {
          irie = final.callCabal2nix "irie" ./. { };
          fresnel = doJailbreak (dontCheck (final.callHackage "fresnel" "0.0.0.1" { fused-effects = null; }));
          derive-storable = final.callHackage "derive-storable" "0.3.0.0" {}; # 0.3.0.1 not available
          derive-storable-plugin = final.callHackage "derive-storable-plugin" "0.2.3.7" {};
#         melf    = final.callHackage "melf" "1.3.0" { };
#         hashable = final.callHackage "hashable" "1.3.5.0" { };
#         fused-effects = final.callHackage "fused-effects" "1.1.2.1" { dontCheck = ["fused-effects"]; };
          })
      ];
      legacyPackages = horizon-platform.legacyPackages.${system}.extend myOverlay;
    in {
      devShells.default = legacyPackages.irie.env.overrideAttrs (attrs: {
        buildInputs = with pkgs; attrs.buildInputs ++ [
          pkgs.cabal-install
        ];
      });
      packages.default = legacyPackages.irie;
    });
}
