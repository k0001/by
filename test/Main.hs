{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -Wno-unused-top-binds -Wno-incomplete-uni-patterns #-}

module Main (main) where

import qualified By
import Control.Monad
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as B8
import Data.Constraint
import Data.Maybe
import Data.Proxy
import Data.Word
import Data.Type.Ord
import GHC.TypeNats
import Hedgehog (MonadGen, forAll, property, (===))
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty (TestTree, testGroup)
import qualified Test.Tasty as Tasty
import Test.Tasty.HUnit (testCase, (@?=), (@=?))
import Test.Tasty.Hedgehog (HedgehogTestLimit (..), testProperty)
import qualified Test.Tasty.Runners as Tasty
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------

main :: IO ()
main =
  Tasty.defaultMainWithIngredients
    [Tasty.consoleTestReporter, Tasty.listingTests]
    $ Tasty.localOption (HedgehogTestLimit (Just 5000)) $
      tt

tt :: TestTree
tt = testGroup "By" [tt_cmp, tt_toFrom, tt_base16, tt_sized, tt_unsized]


tt_unsized :: TestTree
tt_unsized = testGroup "Unsized"
  [ testCase "pack/0" $ By.pack [] @?= Just (B.pack [])
  , testCase "pack/1" $ By.pack [0xAB] @?= Just (B.pack [0xAB])
  , testCase "pack/2" $ By.pack [0xAB, 0xCD] @?= Just (B.pack [0xAB, 0xCD])
  ]

tt_sized :: TestTree
tt_sized = testGroup "Sized"
  [ testCase "pack/0" $
      let Just x =   By.pack @B.ByteString              []
      in  Just x @=? fmap By.unSized (By.pack @(By.Sized 0 B.ByteString) [])
  , testCase "pack/1" $
      let Just x =   By.pack @B.ByteString              [0xAB]
      in  Just x @=? fmap By.unSized (By.pack @(By.Sized 1 B.ByteString) [0xAB])
  , testCase "pack/2" $
      let Just x =   By.pack @B.ByteString              [0xAB, 0xCD]
      in  Just x @=? fmap By.unSized (By.pack @(By.Sized 2 B.ByteString) [0xAB, 0xCD])
  , testCase "takeN" $ By.takeN s8 @?= s2l
  , testCase "dropN" $ By.dropN s8 @?= s6r
  , testCase "splitAtN" $ By.splitAtN s8 @?= (s2l, s6r)
  ]
  where
    s8 :: By.Sized 8 B.ByteString
    Just s8 = By.pack [0, 1, 2, 3, 4, 5, 6, 7]
    s2l :: By.Sized 2 B.ByteString
    Just s2l = By.pack [0, 1]
    s6r :: By.Sized 6 B.ByteString
    Just s6r = By.pack [2, 3, 4, 5, 6, 7]

tt_cmp :: TestTree
tt_cmp =
  testGroup
    "cmp"
    [ testGroup
        "copyN"
        [ testProperty "Ord" $
            property $ do
              x :: B.ByteString <- forAll $ Gen.bytes (Range.linear 0 20)
              y :: B.ByteString <- forAll $ Gen.bytes (Range.linear 0 20)
              compare x y === compare (By.copyN x) (By.copyN y :: B.ByteString)

        , testProperty "Eq" $
            property $ do
              x :: B.ByteString <- forAll $ Gen.bytes (Range.linear 0 20)
              y :: B.ByteString <- forAll $ Gen.bytes (Range.linear 0 20)
              (x == y) === (By.copyN x == (By.copyN y :: B.ByteString))
        ]
    , testGroup
        "Sized len Byets"
        [ testProperty "Ord" $
            property $ do
              a0   <- forAll $ genSizedByteString @0
              a1   <- forAll $ genSizedByteString @1
              a2   <- forAll $ genSizedByteString @2
              a8   <- forAll $ genSizedByteString @8
              a100 <- forAll $ genSizedByteString @100

              b0   <- forAll $ genSizedByteString @0
              b1   <- forAll $ genSizedByteString @1
              b2   <- forAll $ genSizedByteString @2
              b8   <- forAll $ genSizedByteString @8
              b100 <- forAll $ genSizedByteString @100

              compare a0   b0   === compare (By.unSized a0)   (By.unSized b0)
              compare a1   b1   === compare (By.unSized a1)   (By.unSized b1)
              compare a2   b2   === compare (By.unSized a2)   (By.unSized b2)
              compare a8   b8   === compare (By.unSized a8)   (By.unSized b8)
              compare a100 b100 === compare (By.unSized a100) (By.unSized b100)

        , testProperty "Eq" $
            property $ do
              a0   <- forAll $ genSizedByteString @0
              a1   <- forAll $ genSizedByteString @1
              a2   <- forAll $ genSizedByteString @2
              a8   <- forAll $ genSizedByteString @8
              a100 <- forAll $ genSizedByteString @100

              b0   <- forAll $ genSizedByteString @0
              b1   <- forAll $ genSizedByteString @1
              b2   <- forAll $ genSizedByteString @2
              b8   <- forAll $ genSizedByteString @8
              b100 <- forAll $ genSizedByteString @100

              (==) a0   b0   === (==) (By.unSized a0)   (By.unSized b0)
              (==) a1   b1   === (==) (By.unSized a1)   (By.unSized b1)
              (==) a2   b2   === (==) (By.unSized a2)   (By.unSized b2)
              (==) a8   b8   === (==) (By.unSized a8)   (By.unSized b8)
              (==) a100 b100 === (==) (By.unSized a100) (By.unSized b100)
        ]
    ]

tt_base16 :: TestTree
tt_base16 =
  testGroup
    "base16"
    [ testProperty "roundtrip" $
        property $ do
          x <- forAll $ Gen.bytes (Range.linear 0 500)
          Just x === (By.fromBase16 =<< (By.toBase16 True  x :: Maybe B.ByteString))
          Just x === (By.fromBase16 =<< (By.toBase16 False x :: Maybe B.ByteString))

    , testProperty "toBase16 == toBase16N" $
        property $ do
          a0 <- forAll $ genSizedByteString @0
          a1 <- forAll $ genSizedByteString @1
          a2 <- forAll $ genSizedByteString @2
          a3 <- forAll $ genSizedByteString @3

          By.toBase16 True a0 ===
            Just (By.unSized (By.toBase16N True a0 :: By.Sized 0 B.ByteString))
          By.toBase16 True a1 ===
            Just (By.unSized (By.toBase16N True a1 :: By.Sized 2 B.ByteString))
          By.toBase16 True a2 ===
            Just (By.unSized (By.toBase16N True a2 :: By.Sized 4 B.ByteString))
          By.toBase16 True a3 ===
            Just (By.unSized (By.toBase16N True a3 :: By.Sized 6 B.ByteString))

          By.toBase16 False a0 ===
            Just (By.unSized (By.toBase16N False a0 :: By.Sized 0 B.ByteString))
          By.toBase16 False a1 ===
            Just (By.unSized (By.toBase16N False a1 :: By.Sized 2 B.ByteString))
          By.toBase16 False a2 ===
            Just (By.unSized (By.toBase16N False a2 :: By.Sized 4 B.ByteString))
          By.toBase16 False a3 ===
            Just (By.unSized (By.toBase16N False a3 :: By.Sized 6 B.ByteString))

    , Tasty.localOption (HedgehogTestLimit (Just 2000)) $ -- Strings are slow
      testProperty "fromBase16: valid" $
        property $ do
          binLength <- forAll $ Gen.int (Range.linear 0 500)
          b16S <- forAll $ replicateM (binLength * 2) $ Gen.element alphabetBase16S
          let b16 = B8.pack b16S :: B.ByteString
          True === isJust (By.fromBase16 b16 :: Maybe B.ByteString)

    , Tasty.localOption (HedgehogTestLimit (Just 100)) $ -- Strings are slow
      testProperty "toBase16 == showStringBase16" $ do
        property $ do
          x <- forAll $ Gen.bytes (Range.linear 0 20000)
          By.toBase16 True  x === Just (B8.pack (By.showStringBase16 True  x ""))
          By.toBase16 False x === Just (B8.pack (By.showStringBase16 False x ""))
    ]
  where
    alphabetBase16S = "0123456789abcdefABCDEF" :: String

tt_toFrom :: TestTree
tt_toFrom =
  testGroup
    "toFrom"
    [ testGroup
      "Word8"
      [ testCase "decodeLE" $ By.decodeLE b8 @?= w8
      , testCase "decodeBE" $ By.decodeBE b8 @?= w8
      ]
    , testGroup
      "Word16"
      [ testCase "decodeLE" $ By.decodeLE le16 @?= w16
      , testCase "decodeBE" $ By.decodeBE be16 @?= w16
      ]
    , testGroup
      "Word32"
      [ testCase "decodeLE" $ By.decodeLE le32 @?= w32
      , testCase "decodeBE" $ By.decodeBE be32 @?= w32
      ]
    , testGroup
      "Word64"
      [ testCase "decodeLE" $ By.decodeLE le64 @?= w64
      , testCase "decodeBE" $ By.decodeBE be64 @?= w64
      , testCase "encodeLE" $ By.encodeLE w64 @?= le64
      , testCase "encodeBE" $ By.encodeBE w64 @?= be64
      ]
--    , testCase "fromWord8" $ By.fromWord8 w8 @?= b8
--    , testProperty "Word8" $
--        property $ do
--          x <- forAll $ Gen.word8 Range.constantBounded
--          x === By.toWord8 (By.fromWord8 x `asTypeOf` b8)
--    , testCase "toWord16le" $ By.toWord16le le16 @?= w16
--    , testCase "fromWord16le" $ By.fromWord16le w16 @?= le16
--    , testProperty "Word16le" $
--        property $ do
--          x <- forAll $ Gen.word16 Range.constantBounded
--          x === By.toWord16le (By.fromWord16le x `asTypeOf` le16)
--    , testCase "toWord16be" $ By.toWord16be be16 @?= w16
--    , testCase "fromWord16be" $ By.fromWord16be w16 @?= be16
--    , testProperty "Word16be" $
--        property $ do
--          x <- forAll $ Gen.word16 Range.constantBounded
--          x === By.toWord16be (By.fromWord16be x `asTypeOf` be16)
--    , testCase "toWord32le" $ By.toWord32le le32 @?= w32
--    , testCase "fromWord32le" $ By.fromWord32le w32 @?= le32
--    , testProperty "Word32le" $
--        property $ do
--          x <- forAll $ Gen.word32 Range.constantBounded
--          x === By.toWord32le (By.fromWord32le x `asTypeOf` le32)
--    , testCase "toWord32be" $ By.toWord32be be32 @?= w32
--    , testCase "fromWord32be" $ By.fromWord32be w32 @?= be32
--    , testProperty "Word32be" $
--        property $ do
--          x <- forAll $ Gen.word32 Range.constantBounded
--          x === By.toWord32be (By.fromWord32be x `asTypeOf` be32)
--    , testCase "toWord64le" $ By.toWord64le le64 @?= w64
--    , testCase "fromWord64le" $ By.fromWord64le w64 @?= le64
--    , testProperty "Word64le" $
--        property $ do
--          x <- forAll $ Gen.word64 Range.constantBounded
--          x === By.toWord64le (By.fromWord64le x `asTypeOf` le64)
--    , testCase "toWord64be" $ By.toWord64be be64 @?= w64
--    , testCase "fromWord64be" $ By.fromWord64be w64 @?= be64
--    , testProperty "Word64be" $
--        property $ do
--          x <- forAll $ Gen.word64 Range.constantBounded
--          x === By.toWord64be (By.fromWord64be x `asTypeOf` be64)
    ]
  where
    w8 = 0x01 :: Word8
    Just b8 = By.sized @1 (B8.pack "\x01")
    w16 = 0x0123 :: Word16
    Just be16 = By.sized @2 (B8.pack "\x01\x23")
    Just le16 = By.sized @2 (B8.pack "\x23\x01")
    w32 = 0x01234567 :: Word32
    Just be32 = By.sized @4 (B8.pack "\x01\x23\x45\x67")
    Just le32 = By.sized @4 (B8.pack "\x67\x45\x23\x01")
    w64 = 0x0123456789abcdef :: Word64
    Just be64 = By.sized @8 (B8.pack "\x01\x23\x45\x67\x89\xAB\xCD\xEF")
    Just le64 = By.sized @8 (B8.pack "\xEF\xCD\xAB\x89\x67\x45\x23\x01")

genSizedByteString
  :: forall len m
  .  (MonadGen m, By.Alloc (By.Sized len B.ByteString))
  => m (By.Sized len B.ByteString)
genSizedByteString = do
  x <- Gen.bytes $ Range.singleton $ fromIntegral (natVal (Proxy @len))
  maybe (error "genSizedByteString: unexpected") pure (By.sized x)

proveLE
  :: (KnownNat l, KnownNat r)
  => Proxy l
  -> Proxy r
  -> Maybe (Dict (l <= r))
proveLE l r = case cmpNat l r of
  EQI -> Just $ unsafeCoerce (Dict @(0 <= 0))
  LTI -> Just $ unsafeCoerce (Dict @(0 <= 1))
  GTI -> Nothing

-- TODO: test Byets

