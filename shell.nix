let pkgs = import ./nix;
in {
  ghc925 = pkgs._here.ghc925._shell;
}
