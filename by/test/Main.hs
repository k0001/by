{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import qualified By
import Control.Monad
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as B8
import Data.Maybe
import Data.Proxy
import Data.Word
import GHC.TypeLits
import Hedgehog (forAll, property, (===))
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty (TestTree, testGroup)
import qualified Test.Tasty as Tasty
import Test.Tasty.HUnit (testCase, (@?=))
import Test.Tasty.Hedgehog (HedgehogTestLimit (..), testProperty)
import qualified Test.Tasty.Runners as Tasty

--------------------------------------------------------------------------------

main :: IO ()
main =
  Tasty.defaultMainWithIngredients
    [Tasty.consoleTestReporter, Tasty.listingTests]
    $ Tasty.localOption (HedgehogTestLimit (Just 15000)) $
      tt

tt :: TestTree
tt = testGroup "Byets" [tt_cmp, tt_toFrom, tt_base16]

tt_cmp :: TestTree
tt_cmp =
  testGroup
    "cmp"
    [ testProperty "Ord" $
        property $ do
          x :: B.ByteString <- forAll $ Gen.bytes (Range.linear 0 20)
          y :: B.ByteString <- forAll $ Gen.bytes (Range.linear 0 20)
          compare x y === compare (By.ByeString x) (By.ByeString y)
    , testProperty "Eq" $
        property $ do
          x :: B.ByteString <- forAll $ Gen.bytes (Range.linear 0 20)
          y :: B.ByteString <- forAll $ Gen.bytes (Range.linear 0 20)
          (x == y) === (By.ByeString x == By.ByeString y)
    ]

tt_base16 :: TestTree
tt_base16 =
  testGroup
    "base16"
    [ testProperty "roundtrip" $
        property $ do
          x <- forAll $ Gen.bytes (Range.linear 0 500)
          Just x === By.fromBase16 (By.toBase16 x :: By.ByeString)
    , testProperty "fromBase16: valid" $
        property $ do
          binLength <- forAll $ Gen.int (Range.linear 0 500)
          b16S <- forAll $ replicateM (binLength * 2) $ Gen.element alphabetBase16S
          let b16 = B8.pack b16S :: B.ByteString
          True === isJust (By.fromBase16 b16 :: Maybe By.ByeString)
    , testProperty "fromBase16/N: random" $
        property $ do
          xb16 <- forAll $ Gen.bytes (Range.constant 0 4)
          let xb16L :: Int = B.length xb16
              binL :: Int = xb16L `div` 2
              okBytes :: Bool = B.all (`elem` B.unpack alphabetBase16) xb16
              okLength :: Bool = even xb16L
              ok :: Bool = okLength && okBytes
              yBin :: Maybe By.ByeString = By.fromBase16 xb16
              yBinN :: Maybe By.ByeString = do
                SomeNat (_ :: Proxy binL) <- someNatVal (fromIntegral binL)
                sb <- By.fromBase16N xb16 :: Maybe (By.Sized binL By.ByeString)
                pure (By.unSized sb)
          yBin === yBinN
          ok === isJust yBin
    ]
  where
    alphabetBase16S = "0123456789abcdefABCDEF" :: String
    alphabetBase16 = B8.pack alphabetBase16S :: B.ByteString

tt_toFrom :: TestTree
tt_toFrom =
  testGroup
    "toFrom"
    [ testCase "toWord8" $ By.toWord8 b8 @?= w8
    , testCase "fromWord8" $ By.fromWord8 w8 @?= b8
    , testProperty "Word8" $
        property $ do
          x <- forAll $ Gen.word8 Range.constantBounded
          x === By.toWord8 (By.fromWord8 x `asTypeOf` b8)
    , testCase "toWord16le" $ By.toWord16le le16 @?= w16
    , testCase "fromWord16le" $ By.fromWord16le w16 @?= le16
    , testProperty "Word16le" $
        property $ do
          x <- forAll $ Gen.word16 Range.constantBounded
          x === By.toWord16le (By.fromWord16le x `asTypeOf` le16)
    , testCase "toWord16be" $ By.toWord16be be16 @?= w16
    , testCase "fromWord16be" $ By.fromWord16be w16 @?= be16
    , testProperty "Word16be" $
        property $ do
          x <- forAll $ Gen.word16 Range.constantBounded
          x === By.toWord16be (By.fromWord16be x `asTypeOf` be16)
    , testCase "toWord32le" $ By.toWord32le le32 @?= w32
    , testCase "fromWord32le" $ By.fromWord32le w32 @?= le32
    , testProperty "Word32le" $
        property $ do
          x <- forAll $ Gen.word32 Range.constantBounded
          x === By.toWord32le (By.fromWord32le x `asTypeOf` le32)
    , testCase "toWord32be" $ By.toWord32be be32 @?= w32
    , testCase "fromWord32be" $ By.fromWord32be w32 @?= be32
    , testProperty "Word32be" $
        property $ do
          x <- forAll $ Gen.word32 Range.constantBounded
          x === By.toWord32be (By.fromWord32be x `asTypeOf` be32)
    , testCase "toWord64le" $ By.toWord64le le64 @?= w64
    , testCase "fromWord64le" $ By.fromWord64le w64 @?= le64
    , testProperty "Word64le" $
        property $ do
          x <- forAll $ Gen.word64 Range.constantBounded
          x === By.toWord64le (By.fromWord64le x `asTypeOf` le64)
    , testCase "toWord64be" $ By.toWord64be be64 @?= w64
    , testCase "fromWord64be" $ By.fromWord64be w64 @?= be64
    , testProperty "Word64be" $
        property $ do
          x <- forAll $ Gen.word64 Range.constantBounded
          x === By.toWord64be (By.fromWord64be x `asTypeOf` be64)
    ]
  where
    w8 = 0x01 :: Word8
    Just b8 = By.fromBase16N @B.ByteString @(By.Sized 1 B.ByteString) (B8.pack "01")
    w16 = 0x0123 :: Word16
    Just be16 = By.fromBase16N @B.ByteString @(By.Sized 2 B.ByteString) (B8.pack "0123")
    Just le16 = By.fromBase16N @B.ByteString @(By.Sized 2 B.ByteString) (B8.pack "2301")
    w32 = 0x01234567 :: Word32
    Just be32 = By.fromBase16N @B.ByteString @(By.Sized 4 B.ByteString) (B8.pack "01234567")
    Just le32 = By.fromBase16N @B.ByteString @(By.Sized 4 B.ByteString) (B8.pack "67452301")
    w64 = 0x0123456789abcdef :: Word64
    Just be64 = By.fromBase16N @B.ByteString @(By.Sized 8 B.ByteString) (B8.pack "0123456789abcdef")
    Just le64 = By.fromBase16N @B.ByteString @(By.Sized 8 B.ByteString) (B8.pack "efcdab8967452301")
