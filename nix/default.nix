let
  sources = import ./sources.nix;

  haskell-overrides = self: super: { 
    by = self.callCabal2nix "by" ../by { }; 

    _shell = super.shellFor {
      withHoogle = false;
      packages = p: [ p.by ];
    };
  };

  pkgs-overlay = self: super: {
    _here = {
      ghc865 = super.haskell.packages.ghc865.override {
        overrides = haskell-overrides;
      };
    };
  };

in import sources.nixpkgs { overlays = [ pkgs-overlay ]; }