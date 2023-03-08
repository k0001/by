#include "by.h"

#ifdef BY_HAVE_WEAK_SYMBOLS
// This “have weak symbols” idea is based on libsodium's, which
// is copyright Frank Denis, under the terms of the ISC licence.

__attribute__((weak)) void _prevent_memcmp_be_ct_lto(const unsigned char *a,
                                                     const unsigned char *b,
                                                     const size_t len);
__attribute__((weak)) void _prevent_memcmp_be_ct_lto(const unsigned char *a,
                                                     const unsigned char *b,
                                                     const size_t len) {
  (void)a;
  (void)b;
  (void)len;
}

__attribute__((weak)) void _prevent_memeql_ct_lto(const unsigned char *a,
                                                  const unsigned char *b,
                                                  const size_t len);
__attribute__((weak)) void _prevent_memeql_ct_lto(const unsigned char *a,
                                                  const unsigned char *b,
                                                  const size_t len) {
  (void)a;
  (void)b;
  (void)len;
}
#endif

int by_memcmp_be_ct(const uint8_t *a, const uint8_t *b, size_t len) {
#ifdef BY_HAVE_WEAK_SYMBOLS
  const unsigned char *a1 = a;
  const unsigned char *b1 = b;
#else
  const volatile unsigned char *volatile a1 =
      (const volatile unsigned char *volatile)a;
  const volatile unsigned char *volatile b1 =
      (const volatile unsigned char *volatile)b;
#endif
  volatile unsigned char gt = 0U;
  volatile unsigned char eq = 1U;
  uint16_t x1, x2;

#ifdef BY_HAVE_WEAK_SYMBOLS
  _prevent_memcmp_be_ct_lto(a1, b1, len);
#endif
  for (size_t i = 0; i < len; i++) {
    x1 = a1[i];
    x2 = b1[i];
    gt |= (((unsigned int)x2 - (unsigned int)x1) >> 8) & eq;
    eq &= (((unsigned int)(x2 ^ x1)) - 1) >> 8;
  }
  return (int)(gt + gt + eq) - 1;
}

bool by_memeql_ct(const uint8_t *a, const uint8_t *b, size_t len) {
#ifdef BY_HAVE_WEAK_SYMBOLS
  const unsigned char *a1 = a;
  const unsigned char *b1 = b;
#else
  const volatile unsigned char *volatile a1 =
      (const volatile unsigned char *volatile)a;
  const volatile unsigned char *volatile b1 =
      (const volatile unsigned char *volatile)b;
#endif

  int ne = 0;
#ifdef BY_HAVE_WEAK_SYMBOLS
  _prevent_memeql_ct_lto(a1, b1, len);
#endif
  for (size_t i = 0; i < len; i++) {
    ne |= a1[i] ^ b1[i];
  }
  return !ne;
}
