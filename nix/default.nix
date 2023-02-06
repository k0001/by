let
  sources = import ./sources.nix;

  ghc-overrides = pkgs: self: super:
    let hs = pkgs.haskell.lib;
    in {
      ListLike = hs.dontCheck super.ListLike;

      by = self.callCabal2nix "by" ../by { };

      _shell = super.shellFor {
        withHoogle = true;
        buildInputs = [ pkgs.cabal-install ];
        packages = p: [ p.by ];
      };
    };

  pkgs-overlay = self: super: {
    _here = {
      ghc925 = super.haskell.packages.ghc925.override {
        overrides = ghc-overrides self;
      };
    };
  };

in import sources.nixpkgs { overlays = [ pkgs-overlay ]; }
