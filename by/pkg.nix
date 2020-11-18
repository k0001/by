{ mkDerivation, base, bytestring, hedgehog, stdenv, tasty
, tasty-hedgehog, tasty-hunit
}:
mkDerivation {
  pname = "by";
  version = "0.1.0";
  src = ./.;
  libraryHaskellDepends = [ base bytestring ];
  testHaskellDepends = [
    base bytestring hedgehog tasty tasty-hedgehog tasty-hunit
  ];
  homepage = "https://github.com/k0001/by";
  description = "Memory things";
  license = stdenv.lib.licenses.asl20;
}
