let pkgs = import ./nix;
in {
  ghc865 = pkgs._here.ghc865.by;
}