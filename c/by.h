#pragma once
#include "by_base16.h"
#include <stdbool.h>

#define BY_HAVE_WEAK_SYMBOLS (!defined(__ELF__) && !defined(__APPLE_CC__))

bool by_memeql_ct(const uint8_t * a, const uint8_t * b, size_t len);
int by_memcmp_be_ct(const uint8_t * a, const uint8_t * b, size_t len);
