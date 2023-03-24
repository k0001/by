{ mkDerivation, base, binary, bytestring, constraints, hedgehog, lib, memzero
, tagged, tasty, tasty-hedgehog, tasty-hunit, i, kind-integer }:
mkDerivation {
  pname = "by";
  version = "0.1.0";
  src = ./.;
  libraryHaskellDepends =
    [ base binary bytestring constraints memzero tagged i kind-integer ];
  testHaskellDepends = [
    base
    bytestring
    constraints
    hedgehog
    memzero
    tagged
    tasty
    tasty-hedgehog
    tasty-hunit
    i
  ];
  homepage = "https://github.com/k0001/by";
  description = "Memory things";
  license = lib.licenses.asl20;
}
