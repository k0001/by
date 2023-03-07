#ifndef _BY_H
#define _BY_H

#include <stddef.h>
#include <stdint.h>

// Encodes Base16. Returns 0 on success.
int by_to_base16(uint8_t *base16, size_t base16_len, const uint8_t *bin);

// Decodes Base16. Returns 0 on success.
int by_from_base16(uint8_t *bin, const uint8_t *base16, size_t base16_len);

#endif
