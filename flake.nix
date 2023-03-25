{
  description = "Haskell 'by' library";

  inputs = {
    nixpkgs.url =
      "github:NixOS/nixpkgs?rev=21eda9bc80bef824a037582b1e5a43ba74e92daa";
    flake-parts.url = "github:hercules-ci/flake-parts";
    hs_i.url = "github:k0001/hs-i";
    hs_i.inputs.nixpkgs.follows = "nixpkgs";
    hs_memzero.url = "github:k0001/hs-memzero";
    hs_memzero.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = inputs@{ ... }:
    inputs.flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ inputs.flake-parts.flakeModules.easyOverlay ];
      systems = [ "x86_64-linux" "i686-linux" "aarch64-linux" ];
      perSystem = { config, pkgs, final, system, ... }: {
        _module.args.pkgs = import inputs.nixpkgs {
          inherit system;
          overlays = [
            inputs.hs_memzero.overlays.default
            inputs.hs_i.overlays.default

            # Why is this necessary? Shouldn't hs_i bring it?
            inputs.hs_i.inputs.hs_kind.overlays.default
          ];
        };
        overlayAttrs = {
          haskell = pkgs.haskell // {
            packageOverrides = pkgs.lib.composeExtensions
              (pkgs.haskell.packageOverrides or (_: _: { }))
              (hself: hsuper: { by = hself.callPackage ./. { }; });
          };
        };
        packages = {
          by__ghc943 = final.pkgs.haskell.packages.ghc943.by;
          default = pkgs.releaseTools.aggregate {
            name = "every output from this flake";
            constituents = [
              config.packages.by__ghc943
              config.packages.by__ghc943.doc
              config.devShells.ghc943
            ];
          };
        };
        devShells = {
          default = config.devShells.ghc943;
          ghc943 = final.pkgs.haskell.packages.ghc943.shellFor {
            packages = p: [ p.by ];
            withHoogle = true;
            nativeBuildInputs = [ pkgs.cabal-install pkgs.cabal2nix ];
          };
        };
      };
    };
}
