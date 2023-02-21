{ mkDerivation, base, bytestring, constraints, ghc-prim, hedgehog
, lib, tagged, tasty, tasty-hedgehog, tasty-hunit
}:
mkDerivation {
  pname = "by";
  version = "0.1.0";
  src = ./.;
  libraryHaskellDepends = [
    base bytestring constraints ghc-prim tagged
  ];
  testHaskellDepends = [
    base bytestring constraints hedgehog tagged tasty tasty-hedgehog
    tasty-hunit
  ];
  homepage = "https://github.com/k0001/by";
  description = "Memory things";
  license = lib.licenses.asl20;
}