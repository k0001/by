#include "by_base16.h"

// This implementation is based on libsodium's, which is
// copyright Frank Denis, under the terms of the ISC licence.

void by_to_base16_lower__scalar(uint8_t *b16, const uint8_t *bin,
                                size_t bin_len) {
  unsigned int x;
  int b, c;
  for (size_t i = 0; i < bin_len; i++) {
    c = bin[i] & 0xf;
    b = bin[i] >> 4;
    x = (uint8_t)(87 + c + (((c - 10) >> 8) & ~38)) << 8 |
        (uint8_t)(87 + b + (((b - 10) >> 8) & ~38));
    b16[i * 2] = (uint8_t)x;
    b16[i * 2 + 1] = (uint8_t)(x >> 8);
  }
}

void by_to_base16_upper__scalar(uint8_t *b16, const uint8_t *bin,
                                size_t bin_len) {
  unsigned int x;
  int b, c;
  for (size_t i = 0; i < bin_len; i++) {
    c = bin[i] & 0xf;
    b = bin[i] >> 4;
    x = (uint8_t)(55 + c + (((c - 10) >> 8) & ~6)) << 8 |
        (uint8_t)(55 + b + (((b - 10) >> 8) & ~6));
    b16[i * 2] = (uint8_t)x;
    b16[i * 2 + 1] = (uint8_t)(x >> 8);
  }
}
/*
:{
f :: Int -> Int -> Int -> Word8 -> String
f x y z a =
  let c = fromIntegral a .&. 0xf :: Int
      b = fromIntegral a `unsafeShiftR` 4 :: Int
      t n = fromIntegral (x + n + (((n - y) `unsafeShiftR` 8) .&. complement z)
:: Int) :: Word8 r = (fromIntegral (t c) `unsafeShiftL` 8) .|. fromIntegral (t
b) :: Int in map (chr . fromIntegral) [fromIntegral r :: Word8, fromIntegral (r
`unsafeShiftR` 8)]

g :: Word8 -> String
g = f 87 10 38
:}
*/
