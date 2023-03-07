{ mkDerivation, base, binary, bytestring, constraints, hedgehog
, lib, memzero, tagged, tasty, tasty-hedgehog, tasty-hunit
}:
mkDerivation {
  pname = "by";
  version = "0.1.0";
  src = ./.;
  libraryHaskellDepends = [
    base binary bytestring constraints memzero tagged
  ];
  testHaskellDepends = [
    base bytestring constraints hedgehog memzero tagged tasty
    tasty-hedgehog tasty-hunit
  ];
  homepage = "https://github.com/k0001/by";
  description = "Memory things";
  license = lib.licenses.asl20;
}
