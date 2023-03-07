{
  description = "Haskell 'by' library";

  inputs = { memzero.url = "github:k0001/hs-memzero"; };

  outputs = { self, nixpkgs, memzero }:
    let
      inherit (nixpkgs) lib;
      hsBy = import ./.;
      hspkgsOverrides = pself: psuper: hself: hsuper: {
        by = hsuper.callPackage hsBy { };
      };
      pkgsOverlay = lib.composeExtensions memzero.pkgsOverlay (pself: psuper: {
        haskell = psuper.haskell // {
          packageOverrides =
            lib.composeExtensions (memzero.hspkgsOverrides pself psuper)
            (hspkgsOverrides pself psuper);
        };
      });
      pkgsFor = system:
        import nixpkgs {
          inherit system;
          overlays = [ pkgsOverlay ];
        };

    in {
      inherit hsBy hspkgsOverrides pkgsOverlay;
      packages = lib.genAttrs [ "x86_64-linux" "i686-linux" "aarch64-linux" ]
        (system:
          let pkgs = pkgsFor system;
          in {
            default = pkgs.releaseTools.aggregate {
              name = "every output from this flake";
              constituents = let
                p = self.packages.${system};
                s = self.devShells.${system};
              in [
                p.hs_by__ghcDefault
                p.hs_by__ghc925
                p.hs_by__ghc943

                p.hs_by__ghcDefault.doc
                p.hs_by__ghc925.doc
                p.hs_by__ghc943.doc

                s.hs_by__ghcDefault
                s.hs_by__ghc925
                s.hs_by__ghc943
              ];
            };
            hs_by__ghcDefault = pkgs.haskellPackages.by;
            hs_by__ghc925 = pkgs.haskell.packages.ghc925.by;
            hs_by__ghc943 = pkgs.haskell.packages.ghc943.by;
          });
      devShells = lib.genAttrs [ "x86_64-linux" "i686-linux" "aarch64-linux" ]
        (system:
          let
            pkgs = pkgsFor system;
            mkShellFor = hpkgs:
              hpkgs.shellFor {
                packages = p: [ p.by ];
                withHoogle = true;
                nativeBuildInputs = [ pkgs.cabal-install pkgs.cabal2nix ];
              };
          in {
            default = self.devShells.${system}.hs_by__ghcDefault;
            hs_by__ghcDefault = mkShellFor pkgs.haskellPackages;
            hs_by__ghc925 = mkShellFor pkgs.haskell.packages.ghc925;
            hs_by__ghc943 = mkShellFor pkgs.haskell.packages.ghc943;
          });
    };

}
