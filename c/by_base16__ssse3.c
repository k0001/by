#include "by_base16.h"
#include <immintrin.h>

// This implementation is based on the one by Daniel Lemire
// https://lemire.me/blog/2022/12/23/fast-base16-encoding/

__attribute__((target("ssse3"))) void
by_to_base16_lower__ssse3(uint8_t *b16, const uint8_t *bin, size_t bin_len) {
  __m128i shuf = _mm_set_epi8('f', 'e', 'd', 'c', 'b', 'a', '9', '8', '7', '6',
                              '5', '4', '3', '2', '1', '0');
  size_t i = 0;
  __m128i maskf = _mm_set1_epi8(0xf);
  while (i + 16 <= bin_len) {
    __m128i input = _mm_loadu_si128((const __m128i *)(bin + i));
    __m128i inputbase = _mm_and_si128(maskf, input);
    __m128i inputs4 = _mm_and_si128(maskf, _mm_srli_epi16(input, 4));
    __m128i firstpart = _mm_unpacklo_epi8(inputs4, inputbase);
    __m128i output1 = _mm_shuffle_epi8(shuf, firstpart);
    __m128i secondpart = _mm_unpackhi_epi8(inputs4, inputbase);
    __m128i output2 = _mm_shuffle_epi8(shuf, secondpart);
    _mm_storeu_si128((__m128i *)(b16), output1);
    b16 += 16;
    _mm_storeu_si128((__m128i *)(b16), output2);
    b16 += 16;
    i += 16;
  }
  by_to_base16_lower__scalar(b16, bin + i, bin_len - i);
}

__attribute__((target("ssse3"))) void
by_to_base16_upper__ssse3(uint8_t *b16, const uint8_t *bin, size_t bin_len) {
  __m128i shuf = _mm_set_epi8('F', 'E', 'D', 'C', 'B', 'A', '9', '8', '7', '6',
                              '5', '4', '3', '2', '1', '0');
  size_t i = 0;
  __m128i maskf = _mm_set1_epi8(0xf);
  while (i + 16 <= bin_len) {
    __m128i input = _mm_loadu_si128((const __m128i *)(bin + i));
    __m128i inputbase = _mm_and_si128(maskf, input);
    __m128i inputs4 = _mm_and_si128(maskf, _mm_srli_epi16(input, 4));
    __m128i firstpart = _mm_unpacklo_epi8(inputs4, inputbase);
    __m128i output1 = _mm_shuffle_epi8(shuf, firstpart);
    __m128i secondpart = _mm_unpackhi_epi8(inputs4, inputbase);
    __m128i output2 = _mm_shuffle_epi8(shuf, secondpart);
    _mm_storeu_si128((__m128i *)(b16), output1);
    b16 += 16;
    _mm_storeu_si128((__m128i *)(b16), output2);
    b16 += 16;
    i += 16;
  }
  by_to_base16_upper__scalar(b16, bin + i, bin_len - i);
}
