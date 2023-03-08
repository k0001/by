#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

// Encodes `bin` as lowercase base16 into `b16`.
// `b16` must be able to hold `bin_len * 2` bytes.
extern void by_to_base16(uint8_t *b16, const uint8_t *bin, size_t bin_len);
void by_to_base16_lower__scalar(uint8_t *b16, const uint8_t *bin,
                                size_t bin_len);
void by_to_base16_lower__ssse3(uint8_t *b16, const uint8_t *bin,
                               size_t bin_len);
void by_to_base16_lower__avx2(uint8_t *b16, const uint8_t *bin, size_t bin_len);

// Encodes `bin` as uppercase base16 into `b16`.
// `b16` must be able to hold `bin_len * 2` bytes.
extern void by_to_base16(uint8_t *b16, const uint8_t *bin, size_t bin_len);
void by_to_base16_upper__scalar(uint8_t *b16, const uint8_t *bin,
                                size_t bin_len);
void by_to_base16_upper__ssse3(uint8_t *b16, const uint8_t *bin,
                               size_t bin_len);
void by_to_base16_upper__avx2(uint8_t *b16, const uint8_t *bin, size_t bin_len);

// Decodes the base16-encoded bytes in `b16` into `bin`.
// Returns 0 on success. `b16` must be able to hold `bin_len * 2` bytes.
int by_from_base16(uint8_t *bin, size_t bin_len, const uint8_t *b16);
