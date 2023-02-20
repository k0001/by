#include "by.h"

int by_to_base16(uint8_t *base16, size_t base16_len, const uint8_t *bin) {
  if (base16_len & 1) return -1;

  size_t bin_len = base16_len >> 1;
  unsigned int x;
  int b;
  int c;

  for (size_t i = 0; i < bin_len; i++) {
    c = bin[i] & 0xf;
    b = bin[i] >> 4;
    x = (uint8_t)(87U + c + (((c - 10U) >> 8) & ~38U)) << 8 |
        (uint8_t)(87U + b + (((b - 10U) >> 8) & ~38U));
    base16[i * 2U] = (uint8_t)x;
    base16[i * 2U + 1U] = (uint8_t)(x >> 8);
  }

  return 0;
}

int by_from_base16(uint8_t *bin, const uint8_t *base16, size_t base16_len) {
  if (base16_len & 1) return -1;

  // size_t bin_len = base16_len / 2;
  size_t bin_pos = (size_t)0U;
  size_t base16_pos = (size_t)0U;
  uint8_t c;
  uint8_t c_acc = 0U;
  uint8_t c_alpha0, c_alpha;
  uint8_t c_num0, c_num;
  uint8_t c_val;
  uint8_t state = 0U;

  while (base16_pos < base16_len) {
    c = (uint8_t)base16[base16_pos];
    c_num = c ^ 48U;
    c_num0 = (c_num - 10U) >> 8;
    c_alpha = (c & ~32U) - 55U;
    c_alpha0 = ((c_alpha - 10U) ^ (c_alpha - 16U)) >> 8;

    if ((c_num0 | c_alpha0) == 0U)
      break;

    c_val = (c_num0 & c_num) | (c_alpha0 & c_alpha);

    if (state == 0U)
      c_acc = c_val * 16U;
    else
      bin[bin_pos++] = c_acc | c_val;

    state = ~state;
    base16_pos++;
  }

  if (state != 0U)
    return -2;

  if (base16_pos != base16_len)
    return -3;

  return 0;
}
