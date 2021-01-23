#ifndef _BY_H
#define _BY_H

#include <stddef.h>
#include <stdint.h>

// Encodes Base16. Returns 0 on success.
int by_to_base16(uint8_t *base16, size_t base16_len, const uint8_t *bin);

// Decodes Base16. Returns 0 on success.
int by_from_base16(uint8_t *bin, const uint8_t *base16, size_t base16_len);

// Lexicogrphical memory comparisson in constant time.
// Returns 0 if equal, -1 if `a` comes first, or 1 if `b` comes first.
int by_memcmp_const(uint8_t *a, size_t a_len, uint8_t *b, size_t b_len);

// 64 bit little-endian store 
void by_store64le(uint8_t dst[8], uint64_t x);

// 64 bit big-endian store 
void by_store64be(uint8_t dst[8], uint64_t x);

// 32 bit little-endian store 
void by_store32le(uint8_t dst[4], uint32_t x);

// 32 bit big-endian store 
void by_store32be(uint8_t dst[4], uint32_t x);

// 16 bit little-endian store 
void by_store16le(uint8_t dst[2], uint16_t x);

// 16 bit big-endian store 
void by_store16be(uint8_t dst[2], uint16_t x);

// 64 bit little-endian load 
uint64_t by_load64le(const uint8_t in[8]);

// 64 bit big-endian load 
uint64_t by_load64be(const uint8_t in[8]);

// 32 bit little-endian load 
uint32_t by_load32le(const uint8_t in[4]);

// 32 bit big-endian load 
uint32_t by_load32be(const uint8_t in[4]);

// 16 bit little-endian load 
uint16_t by_load16le(const uint8_t in[2]);

// 16 bit big-endian load 
uint16_t by_load16be(const uint8_t in[2]);

#endif
