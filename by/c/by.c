#include "by.h"
#include <string.h>

// The base16 code is based on code from libsodium, whose license (ISC) 
// is at https://raw.githubusercontent.com/jedisct1/libsodium/master/LICENSE

int by_memcmp_const(uint8_t *a, size_t a_len, uint8_t *b, size_t b_len) {
  int ret = 0;

  size_t min_len = a_len < b_len ? a_len : b_len;
  for (size_t i = 0; i < min_len; i++) {
    int x = memcmp(a + i, b + i, 1);
    ret = ret == 0 ? x : ret;
  }

  if (a_len < b_len)
    ret = ret == 0 ? -1 : ret;
  if (a_len > b_len)
    ret = ret == 0 ? 1 : ret;

  return ret;
}

int by_to_base16(uint8_t *base16, size_t base16_len, const uint8_t *bin) {
  if (0 != base16_len % 2)
    return -1;

  size_t bin_len = base16_len / 2;
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
  if (0 != base16_len % 2)
    return -1;

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

void by_store64le(uint8_t out[8], uint64_t x) {
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  *(uint64_t *)out = x;
#else
  out[0] = x;
  out[1] = x >> 8;
  out[2] = x >> 16;
  out[3] = x >> 24;
  out[4] = x >> 32;
  out[5] = x >> 40;
  out[6] = x >> 48;
  out[7] = x >> 56;
#endif
}

void by_store64be(uint8_t out[8], uint64_t x) {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  *(uint64_t *)out = x;
#else
  out[0] = x >> 56;
  out[1] = x >> 48;
  out[2] = x >> 40;
  out[3] = x >> 32;
  out[4] = x >> 24;
  out[5] = x >> 16;
  out[6] = x >> 8;
  out[7] = x;
#endif
}

void by_store32le(uint8_t out[4], uint32_t x) {
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  *(uint32_t *)out = x;
#else
  out[0] = x;
  out[1] = x >> 8;
  out[2] = x >> 16;
  out[3] = x >> 24;
#endif
}

void by_store32be(uint8_t out[4], uint32_t x) {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  *(uint32_t *)out = x;
#else
  out[0] = x >> 24;
  out[1] = x >> 16;
  out[2] = x >> 8;
  out[3] = x;
#endif
}

void by_store16le(uint8_t out[2], uint16_t x) {
#if __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
  *(uint16_t *)out = x;
#else
  out[0] = x;
  out[1] = x >> 8;
#endif
}

void by_store16be(uint8_t out[2], uint16_t x) {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  *(uint16_t *)out = x;
#else
  out[0] = x >> 8;
  out[1] = x;
#endif
}

uint64_t by_load64le(uint8_t in[8]) {
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return *(uint64_t *)in;
#else
  return ((uint64_t)in[0]) |
         ((uint64_t)in[1] << 8) |
         ((uint64_t)in[2] << 16) |
         ((uint64_t)in[3] << 24) |
         ((uint64_t)in[4] << 32) |
         ((uint64_t)in[5] << 40) |
         ((uint64_t)in[6] << 48) |
         ((uint64_t)in[7] << 56);
#endif
}

uint64_t by_load64be(uint8_t in[8]) {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  return *(uint64_t *)in;
#else
  return ((uint64_t)in[0] << 56) |
         ((uint64_t)in[1] << 48) |
         ((uint64_t)in[2] << 40) |
         ((uint64_t)in[3] << 32) |
         ((uint64_t)in[4] << 24) |
         ((uint64_t)in[5] << 16) |
         ((uint64_t)in[6] << 8) |
         ((uint64_t)in[7]);
#endif
}

uint32_t by_load32le(uint8_t in[8]) {
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return *(uint32_t *)in;
#else
  return ((uint32_t)in[0]) |
         ((uint32_t)in[1] << 8) |
         ((uint32_t)in[2] << 16) |
         ((uint32_t)in[3] << 24);
#endif
}

uint32_t by_load32be(uint8_t in[8]) {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  return *(uint32_t *)in;
#else
  return ((uint32_t)in[0] << 24) |
         ((uint32_t)in[1] << 16) |
         ((uint32_t)in[2] << 8) |
         ((uint32_t)in[3]);
#endif
}

uint16_t by_load16le(uint8_t in[8]) {
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return *(uint16_t *)in;
#else
  return ((uint16_t)in[0]) |
         ((uint16_t)in[1] << 8);
#endif
}

uint16_t by_load16be(uint8_t in[8]) {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  return *(uint16_t *)in;
#else
  return ((uint16_t)in[0] << 8) |
         ((uint16_t)in[1]);
#endif
}
