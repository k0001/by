#include "by.h"
#include <string.h>

// The base16 code is based on code from libsodium, whose license (ISC)
// is at https://raw.githubusercontent.com/jedisct1/libsodium/master/LICENSE

int by_memcmp_const(uint8_t *a, size_t a_len, uint8_t *b, size_t b_len) {
  int ret = 0;

  size_t min_len = a_len < b_len ? a_len : b_len;
  for (size_t i = 0; i < min_len; i++) {
    int diff = a[i] - b[i];
    // TODO remove these ifs
    if (diff < 0) ret = ret == 0 ? -1 : ret;
    if (diff > 0) ret = ret == 0 ?  1 : ret;
  }

  // TODO remove these ifs
  if (a_len < b_len) ret = ret == 0 ? -1 : ret;
  if (a_len > b_len) ret = ret == 0 ?  1 : ret;

  return ret;
}

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

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#  define HTOLE16(x) x
#  define LE16TOH(x) x
#  define HTOLE32(x) x
#  define LE32TOH(x) x
#  define HTOLE64(x) x
#  define LE64TOH(x) x
#  define HTOBE16(x) __builtin_bswap16(x)
#  define BE16TOH(x) __builtin_bswap16(x)
#  define HTOBE32(x) __builtin_bswap32(x)
#  define BE32TOH(x) __builtin_bswap32(x)
#  define HTOBE64(x) __builtin_bswap64(x)
#  define BE64TOH(x) __builtin_bswap64(x)
#elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
#  define HTOBE16(x) x
#  define BE16TOH(x) x
#  define HTOBE32(x) x
#  define BE32TOH(x) x
#  define HTOBE64(x) x
#  define BE64TOH(x) x
#  define HTOLE16(x) __builtin_bswap16(x)
#  define LE16TOH(x) __builtin_bswap16(x)
#  define HTOLE32(x) __builtin_bswap32(x)
#  define LE32TOH(x) __builtin_bswap32(x)
#  define HTOLE64(x) __builtin_bswap64(x)
#  define LE64TOH(x) __builtin_bswap64(x)
#else
#  error Unknown __BYTE_ORDER__
#endif

inline void by_store64le(uint8_t dst[8], uint64_t x) {
  ((uint64_t*)dst)[0] = HTOLE64(x);
}
inline void by_store64be(uint8_t dst[8], uint64_t x) {
  ((uint64_t*)dst)[0] = HTOBE64(x);
}
inline void by_store32le(uint8_t dst[4], uint32_t x) {
  ((uint32_t*)dst)[0] = HTOLE32(x);
}
inline void by_store32be(uint8_t dst[4], uint32_t x) {
  ((uint32_t*)dst)[0] = HTOBE32(x);
}
inline void by_store16le(uint8_t dst[2], uint16_t x) {
  ((uint16_t*)dst)[0] = HTOLE16(x);
}
inline void by_store16be(uint8_t dst[2], uint16_t x) {
  ((uint16_t*)dst)[0] = HTOBE16(x);
}

inline uint64_t by_load64le(const uint8_t in[8]) {
  return LE64TOH(((uint64_t*)in)[0]);
}
inline uint64_t by_load64be(const uint8_t in[8]) {
  return BE64TOH(((uint64_t*)in)[0]);
}
inline uint32_t by_load32le(const uint8_t in[4]) {
  return LE32TOH(((uint32_t*)in)[0]);
}
inline uint32_t by_load32be(const uint8_t in[4]) {
  return BE32TOH(((uint32_t*)in)[0]);
}
inline uint16_t by_load16le(const uint8_t in[2]) {
  return LE16TOH(((uint16_t*)in)[0]);
}
inline uint16_t by_load16be(const uint8_t in[2]) {
  return BE16TOH(((uint16_t*)in)[0]);
}
