{
  description = "Haskell 'by' library";

  inputs = {
    memzero = {
      url = "github:k0001/hs-memzero";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    i = {
      url = "github:k0001/hs-i";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, memzero, i }:
    let
      inherit (nixpkgs) lib;
      hs_by = import ./.;
      hspkgsOverrides = pself: psuper: hself: hsuper: {
        by = hsuper.callPackage hs_by { };
      };
      pkgsOverlay = lib.composeExtensions
        (lib.composeExtensions i.pkgsOverlay memzero.pkgsOverlay)
        (pself: psuper: {
          haskell = psuper.haskell // {
            packageOverrides = lib.composeExtensions
              (lib.composeExtensions (i.hspkgsOverrides pself psuper)
                (memzero.hspkgsOverrides pself psuper))
              (hspkgsOverrides pself psuper);
          };
        });
      pkgsFor = system:
        import nixpkgs {
          inherit system;
          overlays = [ pkgsOverlay ];
        };

    in {
      inherit hs_by hspkgsOverrides pkgsOverlay;
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
                # p.hs_by__ghcDefault
                p.hs_by__ghc943

                # p.hs_by__ghcDefault.doc
                p.hs_by__ghc943.doc

                # s.hs_by__ghcDefault
                s.hs_by__ghc943
              ];
            };
            #hs_by__ghcDefault = pkgs.haskellPackages.by;
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
            default = self.devShells.${system}.hs_by__ghc943;
            #hs_by__ghcDefault = mkShellFor pkgs.haskellPackages;
            hs_by__ghc943 = mkShellFor pkgs.haskell.packages.ghc943;
          });
    };

}
