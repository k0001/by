#include "by_base16.h"

#ifndef BY_BASE16_NO_AVX2
#define BY_BASE16_NO_AVX2 0
#endif
#ifndef BY_BASE16_NO_SSSE3
#define BY_BASE16_NO_SSSE3 0
#endif

static void (*by_to_base16_lower__ifunc(void))(uint8_t *, const uint8_t *,
                                               size_t) {
  __builtin_cpu_init();
  if (!BY_BASE16_NO_AVX2 && __builtin_cpu_supports("avx2"))
    return by_to_base16_lower__avx2;
  if (!BY_BASE16_NO_SSSE3 && __builtin_cpu_supports("ssse3"))
    return by_to_base16_lower__ssse3;
  return by_to_base16_lower__scalar;
}

void by_to_base16_lower(uint8_t *, const uint8_t *, size_t)
    __attribute__((ifunc("by_to_base16_lower__ifunc")));

static void (*by_to_base16_upper__ifunc(void))(uint8_t *, const uint8_t *,
                                               size_t) {
  __builtin_cpu_init();
  if (!BY_BASE16_NO_AVX2 && __builtin_cpu_supports("avx2"))
    return by_to_base16_upper__avx2;
  if (!BY_BASE16_NO_SSSE3 && __builtin_cpu_supports("ssse3"))
    return by_to_base16_upper__ssse3;
  return by_to_base16_upper__scalar;
}

void by_to_base16_upper(uint8_t *, const uint8_t *, size_t)
    __attribute__((ifunc("by_to_base16_upper__ifunc")));

// This implementation is based on libsodium's, which is
// copyright Frank Denis, under the terms of the ISC licence.
int by_from_base16(uint8_t *bin, size_t bin_len, const uint8_t *b16) {
  size_t bin_pos = 0;
  uint8_t c;
  uint8_t c_acc = 0;
  uint8_t c_alpha0, c_alpha;
  uint8_t c_num0, c_num;
  uint8_t c_val;
  uint8_t state = 0;

  while (bin_pos < bin_len) {
    c = *b16;
    c_num = c ^ 48;
    c_num0 = (c_num - 10) >> 8;
    c_alpha = (c & ~32) - 55;
    c_alpha0 = ((c_alpha - 10) ^ (c_alpha - 16)) >> 8;
    if ((c_num0 | c_alpha0) == 0)
      break;
    c_val = (c_num0 & c_num) | (c_alpha0 & c_alpha);
    if (state == 0)
      c_acc = c_val * 16;
    else
      bin[bin_pos++] = c_acc | c_val;
    state = ~state;
    b16++;
  }
  if (state != 0)
    return -2;
  if (bin_pos != bin_len)
    return -3;
  return 0;
}
