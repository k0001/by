#include "by_base16.h"
#include <immintrin.h>

// This implementation is based on the one by Daniel Lemire
// https://lemire.me/blog/2022/12/23/fast-base16-encoding/

__attribute__((target("avx2"))) void
by_to_base16_lower__avx2(uint8_t *b16, const uint8_t *bin, size_t bin_len) {
  __m256i shuf =
      _mm256_set_epi8('f', 'e', 'd', 'c', 'b', 'a', '9', '8', '7', '6', '5',
                      '4', '3', '2', '1', '0', 'f', 'e', 'd', 'c', 'b', 'a',
                      '9', '8', '7', '6', '5', '4', '3', '2', '1', '0');
  size_t i = 0;
  __m256i maskf = _mm256_set1_epi8(0xf);
  while (i + 32 <= bin_len) {
    __m256i input = _mm256_loadu_si256((const __m256i *)(bin + i));
    input = _mm256_permute4x64_epi64(input, 0b11011000);
    __m256i inputbase = _mm256_and_si256(maskf, input);
    __m256i inputs4 = _mm256_and_si256(maskf, _mm256_srli_epi16(input, 4));
    __m256i firstpart = _mm256_unpacklo_epi8(inputs4, inputbase);
    __m256i output1 = _mm256_shuffle_epi8(shuf, firstpart);
    __m256i secondpart = _mm256_unpackhi_epi8(inputs4, inputbase);
    __m256i output2 = _mm256_shuffle_epi8(shuf, secondpart);
    _mm256_storeu_si256((__m256i *)(b16), output1);
    b16 += 32;
    _mm256_storeu_si256((__m256i *)(b16), output2);
    b16 += 32;
    i += 32;
  }
  by_to_base16_lower__scalar(b16, bin + i, bin_len - i);
}

__attribute__((target("avx2"))) void
by_to_base16_upper__avx2(uint8_t *b16, const uint8_t *bin, size_t bin_len) {
  __m256i shuf =
      _mm256_set_epi8('F', 'E', 'D', 'C', 'B', 'A', '9', '8', '7', '6', '5',
                      '4', '3', '2', '1', '0', 'F', 'E', 'D', 'C', 'B', 'A',
                      '9', '8', '7', '6', '5', '4', '3', '2', '1', '0');
  size_t i = 0;
  __m256i maskf = _mm256_set1_epi8(0xf);
  while (i + 32 <= bin_len) {
    __m256i input = _mm256_loadu_si256((const __m256i *)(bin + i));
    input = _mm256_permute4x64_epi64(input, 0b11011000);
    __m256i inputbase = _mm256_and_si256(maskf, input);
    __m256i inputs4 = _mm256_and_si256(maskf, _mm256_srli_epi16(input, 4));
    __m256i firstpart = _mm256_unpacklo_epi8(inputs4, inputbase);
    __m256i output1 = _mm256_shuffle_epi8(shuf, firstpart);
    __m256i secondpart = _mm256_unpackhi_epi8(inputs4, inputbase);
    __m256i output2 = _mm256_shuffle_epi8(shuf, secondpart);
    _mm256_storeu_si256((__m256i *)(b16), output1);
    b16 += 32;
    _mm256_storeu_si256((__m256i *)(b16), output2);
    b16 += 32;
    i += 32;
  }
  by_to_base16_upper__scalar(b16, bin + i, bin_len - i);
}
