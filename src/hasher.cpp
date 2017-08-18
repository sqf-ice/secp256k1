#include <endian.h>
#include <stdint.h>
#include <string.h>

#include <x86intrin.h>

#include "hasher.h"

uint32_t static inline ReadLE32(const unsigned char* ptr)
{
    uint32_t x;
    memcpy((char*)&x, ptr, 4);
    return le32toh(x);
}

void static inline WriteLE32(unsigned char* ptr, uint32_t x)
{
    uint32_t v = htole32(x);
    memcpy(ptr, (char*)&v, 4);
}

uint32_t static inline ReadBE32(const unsigned char* ptr)
{
    uint32_t x;
    memcpy((char*)&x, ptr, 4);
    return be32toh(x);
}

void static inline WriteBE32(unsigned char* ptr, uint32_t x)
{
    uint32_t v = htobe32(x);
    memcpy(ptr, (char*)&v, 4);
}

namespace ripemd160 {
// Internal implementation code.
namespace
{
uint32_t inline f1(uint32_t x, uint32_t y, uint32_t z) { return x ^ y ^ z; }
uint32_t inline f2(uint32_t x, uint32_t y, uint32_t z) { return (x & y) | (~x & z); }
uint32_t inline f3(uint32_t x, uint32_t y, uint32_t z) { return (x | ~y) ^ z; }
uint32_t inline f4(uint32_t x, uint32_t y, uint32_t z) { return (x & z) | (y & ~z); }
uint32_t inline f5(uint32_t x, uint32_t y, uint32_t z) { return x ^ (y | ~z); }

uint32_t inline rol(uint32_t x, int i) { return (x << i) | (x >> (32 - i)); }

void inline Round(uint32_t& a, uint32_t b, uint32_t& c, uint32_t d, uint32_t e, uint32_t f, uint32_t x, uint32_t k, int r)
{
    a = rol(a + f + x + k, r) + e;
    c = rol(c, 10);
}

void inline R11(uint32_t& a, uint32_t b, uint32_t& c, uint32_t d, uint32_t e, uint32_t x, int r) { Round(a, b, c, d, e, f1(b, c, d), x, 0, r); }
void inline R21(uint32_t& a, uint32_t b, uint32_t& c, uint32_t d, uint32_t e, uint32_t x, int r) { Round(a, b, c, d, e, f2(b, c, d), x, 0x5A827999ul, r); }
void inline R31(uint32_t& a, uint32_t b, uint32_t& c, uint32_t d, uint32_t e, uint32_t x, int r) { Round(a, b, c, d, e, f3(b, c, d), x, 0x6ED9EBA1ul, r); }
void inline R41(uint32_t& a, uint32_t b, uint32_t& c, uint32_t d, uint32_t e, uint32_t x, int r) { Round(a, b, c, d, e, f4(b, c, d), x, 0x8F1BBCDCul, r); }
void inline R51(uint32_t& a, uint32_t b, uint32_t& c, uint32_t d, uint32_t e, uint32_t x, int r) { Round(a, b, c, d, e, f5(b, c, d), x, 0xA953FD4Eul, r); }

void inline R12(uint32_t& a, uint32_t b, uint32_t& c, uint32_t d, uint32_t e, uint32_t x, int r) { Round(a, b, c, d, e, f5(b, c, d), x, 0x50A28BE6ul, r); }
void inline R22(uint32_t& a, uint32_t b, uint32_t& c, uint32_t d, uint32_t e, uint32_t x, int r) { Round(a, b, c, d, e, f4(b, c, d), x, 0x5C4DD124ul, r); }
void inline R32(uint32_t& a, uint32_t b, uint32_t& c, uint32_t d, uint32_t e, uint32_t x, int r) { Round(a, b, c, d, e, f3(b, c, d), x, 0x6D703EF3ul, r); }
void inline R42(uint32_t& a, uint32_t b, uint32_t& c, uint32_t d, uint32_t e, uint32_t x, int r) { Round(a, b, c, d, e, f2(b, c, d), x, 0x7A6D76E9ul, r); }
void inline R52(uint32_t& a, uint32_t b, uint32_t& c, uint32_t d, uint32_t e, uint32_t x, int r) { Round(a, b, c, d, e, f1(b, c, d), x, 0, r); }

}

/** Perform a RIPEMD-160 transformation, processing a 64-byte chunk. */
void Transform(unsigned char* out, const unsigned char* chunk)
{
    uint32_t a1 = 0x67452301ul, b1 = 0xEFCDAB89ul, c1 = 0x98BADCFEul, d1 = 0x10325476ul, e1 = 0xC3D2E1F0ul;
    uint32_t a2 = 0x67452301ul, b2 = 0xEFCDAB89ul, c2 = 0x98BADCFEul, d2 = 0x10325476ul, e2 = 0xC3D2E1F0ul;
    uint32_t w0 = ReadLE32(chunk + 0), w1 = ReadLE32(chunk + 4), w2 = ReadLE32(chunk + 8), w3 = ReadLE32(chunk + 12);
    uint32_t w4 = ReadLE32(chunk + 16), w5 = ReadLE32(chunk + 20), w6 = ReadLE32(chunk + 24), w7 = ReadLE32(chunk + 28);
    uint32_t w8 = ReadLE32(chunk + 32), w9 = ReadLE32(chunk + 36), w10 = ReadLE32(chunk + 40), w11 = ReadLE32(chunk + 44);
    uint32_t w12 = ReadLE32(chunk + 48), w13 = ReadLE32(chunk + 52), w14 = ReadLE32(chunk + 56), w15 = ReadLE32(chunk + 60);

    R11(a1, b1, c1, d1, e1, w0, 11);
    R12(a2, b2, c2, d2, e2, w5, 8);
    R11(e1, a1, b1, c1, d1, w1, 14);
    R12(e2, a2, b2, c2, d2, w14, 9);
    R11(d1, e1, a1, b1, c1, w2, 15);
    R12(d2, e2, a2, b2, c2, w7, 9);
    R11(c1, d1, e1, a1, b1, w3, 12);
    R12(c2, d2, e2, a2, b2, w0, 11);
    R11(b1, c1, d1, e1, a1, w4, 5);
    R12(b2, c2, d2, e2, a2, w9, 13);
    R11(a1, b1, c1, d1, e1, w5, 8);
    R12(a2, b2, c2, d2, e2, w2, 15);
    R11(e1, a1, b1, c1, d1, w6, 7);
    R12(e2, a2, b2, c2, d2, w11, 15);
    R11(d1, e1, a1, b1, c1, w7, 9);
    R12(d2, e2, a2, b2, c2, w4, 5);
    R11(c1, d1, e1, a1, b1, w8, 11);
    R12(c2, d2, e2, a2, b2, w13, 7);
    R11(b1, c1, d1, e1, a1, w9, 13);
    R12(b2, c2, d2, e2, a2, w6, 7);
    R11(a1, b1, c1, d1, e1, w10, 14);
    R12(a2, b2, c2, d2, e2, w15, 8);
    R11(e1, a1, b1, c1, d1, w11, 15);
    R12(e2, a2, b2, c2, d2, w8, 11);
    R11(d1, e1, a1, b1, c1, w12, 6);
    R12(d2, e2, a2, b2, c2, w1, 14);
    R11(c1, d1, e1, a1, b1, w13, 7);
    R12(c2, d2, e2, a2, b2, w10, 14);
    R11(b1, c1, d1, e1, a1, w14, 9);
    R12(b2, c2, d2, e2, a2, w3, 12);
    R11(a1, b1, c1, d1, e1, w15, 8);
    R12(a2, b2, c2, d2, e2, w12, 6);

    R21(e1, a1, b1, c1, d1, w7, 7);
    R22(e2, a2, b2, c2, d2, w6, 9);
    R21(d1, e1, a1, b1, c1, w4, 6);
    R22(d2, e2, a2, b2, c2, w11, 13);
    R21(c1, d1, e1, a1, b1, w13, 8);
    R22(c2, d2, e2, a2, b2, w3, 15);
    R21(b1, c1, d1, e1, a1, w1, 13);
    R22(b2, c2, d2, e2, a2, w7, 7);
    R21(a1, b1, c1, d1, e1, w10, 11);
    R22(a2, b2, c2, d2, e2, w0, 12);
    R21(e1, a1, b1, c1, d1, w6, 9);
    R22(e2, a2, b2, c2, d2, w13, 8);
    R21(d1, e1, a1, b1, c1, w15, 7);
    R22(d2, e2, a2, b2, c2, w5, 9);
    R21(c1, d1, e1, a1, b1, w3, 15);
    R22(c2, d2, e2, a2, b2, w10, 11);
    R21(b1, c1, d1, e1, a1, w12, 7);
    R22(b2, c2, d2, e2, a2, w14, 7);
    R21(a1, b1, c1, d1, e1, w0, 12);
    R22(a2, b2, c2, d2, e2, w15, 7);
    R21(e1, a1, b1, c1, d1, w9, 15);
    R22(e2, a2, b2, c2, d2, w8, 12);
    R21(d1, e1, a1, b1, c1, w5, 9);
    R22(d2, e2, a2, b2, c2, w12, 7);
    R21(c1, d1, e1, a1, b1, w2, 11);
    R22(c2, d2, e2, a2, b2, w4, 6);
    R21(b1, c1, d1, e1, a1, w14, 7);
    R22(b2, c2, d2, e2, a2, w9, 15);
    R21(a1, b1, c1, d1, e1, w11, 13);
    R22(a2, b2, c2, d2, e2, w1, 13);
    R21(e1, a1, b1, c1, d1, w8, 12);
    R22(e2, a2, b2, c2, d2, w2, 11);

    R31(d1, e1, a1, b1, c1, w3, 11);
    R32(d2, e2, a2, b2, c2, w15, 9);
    R31(c1, d1, e1, a1, b1, w10, 13);
    R32(c2, d2, e2, a2, b2, w5, 7);
    R31(b1, c1, d1, e1, a1, w14, 6);
    R32(b2, c2, d2, e2, a2, w1, 15);
    R31(a1, b1, c1, d1, e1, w4, 7);
    R32(a2, b2, c2, d2, e2, w3, 11);
    R31(e1, a1, b1, c1, d1, w9, 14);
    R32(e2, a2, b2, c2, d2, w7, 8);
    R31(d1, e1, a1, b1, c1, w15, 9);
    R32(d2, e2, a2, b2, c2, w14, 6);
    R31(c1, d1, e1, a1, b1, w8, 13);
    R32(c2, d2, e2, a2, b2, w6, 6);
    R31(b1, c1, d1, e1, a1, w1, 15);
    R32(b2, c2, d2, e2, a2, w9, 14);
    R31(a1, b1, c1, d1, e1, w2, 14);
    R32(a2, b2, c2, d2, e2, w11, 12);
    R31(e1, a1, b1, c1, d1, w7, 8);
    R32(e2, a2, b2, c2, d2, w8, 13);
    R31(d1, e1, a1, b1, c1, w0, 13);
    R32(d2, e2, a2, b2, c2, w12, 5);
    R31(c1, d1, e1, a1, b1, w6, 6);
    R32(c2, d2, e2, a2, b2, w2, 14);
    R31(b1, c1, d1, e1, a1, w13, 5);
    R32(b2, c2, d2, e2, a2, w10, 13);
    R31(a1, b1, c1, d1, e1, w11, 12);
    R32(a2, b2, c2, d2, e2, w0, 13);
    R31(e1, a1, b1, c1, d1, w5, 7);
    R32(e2, a2, b2, c2, d2, w4, 7);
    R31(d1, e1, a1, b1, c1, w12, 5);
    R32(d2, e2, a2, b2, c2, w13, 5);

    R41(c1, d1, e1, a1, b1, w1, 11);
    R42(c2, d2, e2, a2, b2, w8, 15);
    R41(b1, c1, d1, e1, a1, w9, 12);
    R42(b2, c2, d2, e2, a2, w6, 5);
    R41(a1, b1, c1, d1, e1, w11, 14);
    R42(a2, b2, c2, d2, e2, w4, 8);
    R41(e1, a1, b1, c1, d1, w10, 15);
    R42(e2, a2, b2, c2, d2, w1, 11);
    R41(d1, e1, a1, b1, c1, w0, 14);
    R42(d2, e2, a2, b2, c2, w3, 14);
    R41(c1, d1, e1, a1, b1, w8, 15);
    R42(c2, d2, e2, a2, b2, w11, 14);
    R41(b1, c1, d1, e1, a1, w12, 9);
    R42(b2, c2, d2, e2, a2, w15, 6);
    R41(a1, b1, c1, d1, e1, w4, 8);
    R42(a2, b2, c2, d2, e2, w0, 14);
    R41(e1, a1, b1, c1, d1, w13, 9);
    R42(e2, a2, b2, c2, d2, w5, 6);
    R41(d1, e1, a1, b1, c1, w3, 14);
    R42(d2, e2, a2, b2, c2, w12, 9);
    R41(c1, d1, e1, a1, b1, w7, 5);
    R42(c2, d2, e2, a2, b2, w2, 12);
    R41(b1, c1, d1, e1, a1, w15, 6);
    R42(b2, c2, d2, e2, a2, w13, 9);
    R41(a1, b1, c1, d1, e1, w14, 8);
    R42(a2, b2, c2, d2, e2, w9, 12);
    R41(e1, a1, b1, c1, d1, w5, 6);
    R42(e2, a2, b2, c2, d2, w7, 5);
    R41(d1, e1, a1, b1, c1, w6, 5);
    R42(d2, e2, a2, b2, c2, w10, 15);
    R41(c1, d1, e1, a1, b1, w2, 12);
    R42(c2, d2, e2, a2, b2, w14, 8);

    R51(b1, c1, d1, e1, a1, w4, 9);
    R52(b2, c2, d2, e2, a2, w12, 8);
    R51(a1, b1, c1, d1, e1, w0, 15);
    R52(a2, b2, c2, d2, e2, w15, 5);
    R51(e1, a1, b1, c1, d1, w5, 5);
    R52(e2, a2, b2, c2, d2, w10, 12);
    R51(d1, e1, a1, b1, c1, w9, 11);
    R52(d2, e2, a2, b2, c2, w4, 9);
    R51(c1, d1, e1, a1, b1, w7, 6);
    R52(c2, d2, e2, a2, b2, w1, 12);
    R51(b1, c1, d1, e1, a1, w12, 8);
    R52(b2, c2, d2, e2, a2, w5, 5);
    R51(a1, b1, c1, d1, e1, w2, 13);
    R52(a2, b2, c2, d2, e2, w8, 14);
    R51(e1, a1, b1, c1, d1, w10, 12);
    R52(e2, a2, b2, c2, d2, w7, 6);
    R51(d1, e1, a1, b1, c1, w14, 5);
    R52(d2, e2, a2, b2, c2, w6, 8);
    R51(c1, d1, e1, a1, b1, w1, 12);
    R52(c2, d2, e2, a2, b2, w2, 13);
    R51(b1, c1, d1, e1, a1, w3, 13);
    R52(b2, c2, d2, e2, a2, w13, 6);
    R51(a1, b1, c1, d1, e1, w8, 14);
    R52(a2, b2, c2, d2, e2, w14, 5);
    R51(e1, a1, b1, c1, d1, w11, 11);
    R52(e2, a2, b2, c2, d2, w0, 15);
    R51(d1, e1, a1, b1, c1, w6, 8);
    R52(d2, e2, a2, b2, c2, w3, 13);
    R51(c1, d1, e1, a1, b1, w15, 5);
    R52(c2, d2, e2, a2, b2, w9, 11);
    R51(b1, c1, d1, e1, a1, w13, 6);
    R52(b2, c2, d2, e2, a2, w11, 11);

    WriteLE32(out, 0xEFCDAB89ul + c1 + d2);
    WriteLE32(out + 4, 0x98BADCFEul + d1 + e2);
    WriteLE32(out + 8, 0x10325476ul + e1 + a2);
    WriteLE32(out + 12, 0xC3D2E1F0ul + a1 + b2);
    WriteLE32(out + 16, 0x67452301ul + b1 + c2);
}

}

namespace ripemd160_8way {
// Internal implementation code.
namespace
{
__m256i inline f1(__m256i x, __m256i y, __m256i z) { return _mm256_xor_si256(_mm256_xor_si256(x, y), z); }
__m256i inline f2(__m256i x, __m256i y, __m256i z) { return _mm256_or_si256(_mm256_and_si256(x, y), _mm256_andnot_si256(x, z)); }
__m256i inline f3(__m256i x, __m256i y, __m256i z) { return _mm256_xor_si256(_mm256_or_si256(~y, x), z); }
__m256i inline f4(__m256i x, __m256i y, __m256i z) { return _mm256_or_si256(_mm256_and_si256(z, x), _mm256_andnot_si256(z, y)); }
__m256i inline f5(__m256i x, __m256i y, __m256i z) { return _mm256_xor_si256(_mm256_or_si256(~z, y), x); }

__m256i inline rol(__m256i x, const int n) { return _mm256_or_si256(_mm256_slli_epi32(x, n),_mm256_srli_epi32(x, 32 - n)); }

__m256i inline add3(__m256i a, __m256i b, __m256i c) { return _mm256_add_epi32(_mm256_add_epi32(a, b), c); }
__m256i inline add4(__m256i a, __m256i b, __m256i c, __m256i d) { return _mm256_add_epi32(_mm256_add_epi32(a, b), _mm256_add_epi32(c, d)); }

void inline Round(__m256i& a, __m256i b, __m256i& c, __m256i d, __m256i e, __m256i f, __m256i x, uint32_t k, int r)
{
    __m256i tmp = _mm256_set1_epi32(k);
    a = _mm256_add_epi32(rol(add4(a, f, x, tmp), r), e);
    c = rol(c, 10);
}

void inline RoundS(__m256i& a, __m256i b, __m256i& c, __m256i d, __m256i e, __m256i f, __m256i x, int r)
{
    a = _mm256_add_epi32(rol(add3(a, f, x), r), e);
    c = rol(c, 10);
}

void inline R11(__m256i& a, __m256i b, __m256i& c, __m256i d, __m256i e, __m256i x, int r) { RoundS(a, b, c, d, e, f1(b, c, d), x, r); }
void inline R21(__m256i& a, __m256i b, __m256i& c, __m256i d, __m256i e, __m256i x, int r) { Round(a, b, c, d, e, f2(b, c, d), x, 0x5A827999ul, r); }
void inline R31(__m256i& a, __m256i b, __m256i& c, __m256i d, __m256i e, __m256i x, int r) { Round(a, b, c, d, e, f3(b, c, d), x, 0x6ED9EBA1ul, r); }
void inline R41(__m256i& a, __m256i b, __m256i& c, __m256i d, __m256i e, __m256i x, int r) { Round(a, b, c, d, e, f4(b, c, d), x, 0x8F1BBCDCul, r); }
void inline R51(__m256i& a, __m256i b, __m256i& c, __m256i d, __m256i e, __m256i x, int r) { Round(a, b, c, d, e, f5(b, c, d), x, 0xA953FD4Eul, r); }

void inline R12(__m256i& a, __m256i b, __m256i& c, __m256i d, __m256i e, __m256i x, int r) { Round(a, b, c, d, e, f5(b, c, d), x, 0x50A28BE6ul, r); }
void inline R22(__m256i& a, __m256i b, __m256i& c, __m256i d, __m256i e, __m256i x, int r) { Round(a, b, c, d, e, f4(b, c, d), x, 0x5C4DD124ul, r); }
void inline R32(__m256i& a, __m256i b, __m256i& c, __m256i d, __m256i e, __m256i x, int r) { Round(a, b, c, d, e, f3(b, c, d), x, 0x6D703EF3ul, r); }
void inline R42(__m256i& a, __m256i b, __m256i& c, __m256i d, __m256i e, __m256i x, int r) { Round(a, b, c, d, e, f2(b, c, d), x, 0x7A6D76E9ul, r); }
void inline R52(__m256i& a, __m256i b, __m256i& c, __m256i d, __m256i e, __m256i x, int r) { RoundS(a, b, c, d, e, f1(b, c, d), x, r); }

__m256i inline Read8(const unsigned char* chunk) {
    return _mm256_set_epi32(ReadLE32(chunk + 0), ReadLE32(chunk + 64), ReadLE32(chunk + 128), ReadLE32(chunk + 192), ReadLE32(chunk + 256), ReadLE32(chunk + 320), ReadLE32(chunk + 384), ReadLE32(chunk + 448));
}

void inline __attribute__((always_inline)) Write8(unsigned char* out0, unsigned char* out1, unsigned char* out2, unsigned char* out3, unsigned char* out4, unsigned char* out5, unsigned char* out6, unsigned char* out7, __m256i v, size_t offset) {
    union { uint32_t ret[8]; __m256i x; } box;
    box.x = v;
    WriteLE32(out0 + offset, box.ret[0]);
    WriteLE32(out1 + offset, box.ret[1]);
    WriteLE32(out2 + offset, box.ret[2]);
    WriteLE32(out3 + offset, box.ret[3]);
    WriteLE32(out4 + offset, box.ret[4]);
    WriteLE32(out5 + offset, box.ret[5]);
    WriteLE32(out6 + offset, box.ret[6]);
    WriteLE32(out7 + offset, box.ret[7]);
}

}

/** Perform a RIPEMD-160 transformation, processing a 64-byte chunk. */
void Transform(unsigned char* out0, unsigned char* out1, unsigned char* out2, unsigned char* out3, unsigned char* out4, unsigned char* out5, unsigned char* out6, unsigned char* out7, const unsigned char* chunk)
{
    __m256i a1 = _mm256_set1_epi32(0x67452301ul), a2 = a1;
    __m256i b1 = _mm256_set1_epi32(0xEFCDAB89ul), b2 = b1;
    __m256i c1 = _mm256_set1_epi32(0x98BADCFEul), c2 = c1;
    __m256i d1 = _mm256_set1_epi32(0x10325476ul), d2 = d1;
    __m256i e1 = _mm256_set1_epi32(0xC3D2E1F0ul), e2 = e1;

    __m256i w0 = Read8(chunk + 0), w1 = Read8(chunk + 4), w2 = Read8(chunk + 8), w3 = Read8(chunk + 12);
    __m256i w4 = Read8(chunk + 16), w5 = Read8(chunk + 20), w6 = Read8(chunk + 24), w7 = Read8(chunk + 28);
    __m256i w8 = Read8(chunk + 32), w9 = Read8(chunk + 36), w10 = Read8(chunk + 40), w11 = Read8(chunk + 44);
    __m256i w12 = Read8(chunk + 48), w13 = Read8(chunk + 52), w14 = Read8(chunk + 56), w15 = Read8(chunk + 60);

    R11(a1, b1, c1, d1, e1, w0, 11);
    R12(a2, b2, c2, d2, e2, w5, 8);
    R11(e1, a1, b1, c1, d1, w1, 14);
    R12(e2, a2, b2, c2, d2, w14, 9);
    R11(d1, e1, a1, b1, c1, w2, 15);
    R12(d2, e2, a2, b2, c2, w7, 9);
    R11(c1, d1, e1, a1, b1, w3, 12);
    R12(c2, d2, e2, a2, b2, w0, 11);
    R11(b1, c1, d1, e1, a1, w4, 5);
    R12(b2, c2, d2, e2, a2, w9, 13);
    R11(a1, b1, c1, d1, e1, w5, 8);
    R12(a2, b2, c2, d2, e2, w2, 15);
    R11(e1, a1, b1, c1, d1, w6, 7);
    R12(e2, a2, b2, c2, d2, w11, 15);
    R11(d1, e1, a1, b1, c1, w7, 9);
    R12(d2, e2, a2, b2, c2, w4, 5);
    R11(c1, d1, e1, a1, b1, w8, 11);
    R12(c2, d2, e2, a2, b2, w13, 7);
    R11(b1, c1, d1, e1, a1, w9, 13);
    R12(b2, c2, d2, e2, a2, w6, 7);
    R11(a1, b1, c1, d1, e1, w10, 14);
    R12(a2, b2, c2, d2, e2, w15, 8);
    R11(e1, a1, b1, c1, d1, w11, 15);
    R12(e2, a2, b2, c2, d2, w8, 11);
    R11(d1, e1, a1, b1, c1, w12, 6);
    R12(d2, e2, a2, b2, c2, w1, 14);
    R11(c1, d1, e1, a1, b1, w13, 7);
    R12(c2, d2, e2, a2, b2, w10, 14);
    R11(b1, c1, d1, e1, a1, w14, 9);
    R12(b2, c2, d2, e2, a2, w3, 12);
    R11(a1, b1, c1, d1, e1, w15, 8);
    R12(a2, b2, c2, d2, e2, w12, 6);

    R21(e1, a1, b1, c1, d1, w7, 7);
    R22(e2, a2, b2, c2, d2, w6, 9);
    R21(d1, e1, a1, b1, c1, w4, 6);
    R22(d2, e2, a2, b2, c2, w11, 13);
    R21(c1, d1, e1, a1, b1, w13, 8);
    R22(c2, d2, e2, a2, b2, w3, 15);
    R21(b1, c1, d1, e1, a1, w1, 13);
    R22(b2, c2, d2, e2, a2, w7, 7);
    R21(a1, b1, c1, d1, e1, w10, 11);
    R22(a2, b2, c2, d2, e2, w0, 12);
    R21(e1, a1, b1, c1, d1, w6, 9);
    R22(e2, a2, b2, c2, d2, w13, 8);
    R21(d1, e1, a1, b1, c1, w15, 7);
    R22(d2, e2, a2, b2, c2, w5, 9);
    R21(c1, d1, e1, a1, b1, w3, 15);
    R22(c2, d2, e2, a2, b2, w10, 11);
    R21(b1, c1, d1, e1, a1, w12, 7);
    R22(b2, c2, d2, e2, a2, w14, 7);
    R21(a1, b1, c1, d1, e1, w0, 12);
    R22(a2, b2, c2, d2, e2, w15, 7);
    R21(e1, a1, b1, c1, d1, w9, 15);
    R22(e2, a2, b2, c2, d2, w8, 12);
    R21(d1, e1, a1, b1, c1, w5, 9);
    R22(d2, e2, a2, b2, c2, w12, 7);
    R21(c1, d1, e1, a1, b1, w2, 11);
    R22(c2, d2, e2, a2, b2, w4, 6);
    R21(b1, c1, d1, e1, a1, w14, 7);
    R22(b2, c2, d2, e2, a2, w9, 15);
    R21(a1, b1, c1, d1, e1, w11, 13);
    R22(a2, b2, c2, d2, e2, w1, 13);
    R21(e1, a1, b1, c1, d1, w8, 12);
    R22(e2, a2, b2, c2, d2, w2, 11);

    R31(d1, e1, a1, b1, c1, w3, 11);
    R32(d2, e2, a2, b2, c2, w15, 9);
    R31(c1, d1, e1, a1, b1, w10, 13);
    R32(c2, d2, e2, a2, b2, w5, 7);
    R31(b1, c1, d1, e1, a1, w14, 6);
    R32(b2, c2, d2, e2, a2, w1, 15);
    R31(a1, b1, c1, d1, e1, w4, 7);
    R32(a2, b2, c2, d2, e2, w3, 11);
    R31(e1, a1, b1, c1, d1, w9, 14);
    R32(e2, a2, b2, c2, d2, w7, 8);
    R31(d1, e1, a1, b1, c1, w15, 9);
    R32(d2, e2, a2, b2, c2, w14, 6);
    R31(c1, d1, e1, a1, b1, w8, 13);
    R32(c2, d2, e2, a2, b2, w6, 6);
    R31(b1, c1, d1, e1, a1, w1, 15);
    R32(b2, c2, d2, e2, a2, w9, 14);
    R31(a1, b1, c1, d1, e1, w2, 14);
    R32(a2, b2, c2, d2, e2, w11, 12);
    R31(e1, a1, b1, c1, d1, w7, 8);
    R32(e2, a2, b2, c2, d2, w8, 13);
    R31(d1, e1, a1, b1, c1, w0, 13);
    R32(d2, e2, a2, b2, c2, w12, 5);
    R31(c1, d1, e1, a1, b1, w6, 6);
    R32(c2, d2, e2, a2, b2, w2, 14);
    R31(b1, c1, d1, e1, a1, w13, 5);
    R32(b2, c2, d2, e2, a2, w10, 13);
    R31(a1, b1, c1, d1, e1, w11, 12);
    R32(a2, b2, c2, d2, e2, w0, 13);
    R31(e1, a1, b1, c1, d1, w5, 7);
    R32(e2, a2, b2, c2, d2, w4, 7);
    R31(d1, e1, a1, b1, c1, w12, 5);
    R32(d2, e2, a2, b2, c2, w13, 5);

    R41(c1, d1, e1, a1, b1, w1, 11);
    R42(c2, d2, e2, a2, b2, w8, 15);
    R41(b1, c1, d1, e1, a1, w9, 12);
    R42(b2, c2, d2, e2, a2, w6, 5);
    R41(a1, b1, c1, d1, e1, w11, 14);
    R42(a2, b2, c2, d2, e2, w4, 8);
    R41(e1, a1, b1, c1, d1, w10, 15);
    R42(e2, a2, b2, c2, d2, w1, 11);
    R41(d1, e1, a1, b1, c1, w0, 14);
    R42(d2, e2, a2, b2, c2, w3, 14);
    R41(c1, d1, e1, a1, b1, w8, 15);
    R42(c2, d2, e2, a2, b2, w11, 14);
    R41(b1, c1, d1, e1, a1, w12, 9);
    R42(b2, c2, d2, e2, a2, w15, 6);
    R41(a1, b1, c1, d1, e1, w4, 8);
    R42(a2, b2, c2, d2, e2, w0, 14);
    R41(e1, a1, b1, c1, d1, w13, 9);
    R42(e2, a2, b2, c2, d2, w5, 6);
    R41(d1, e1, a1, b1, c1, w3, 14);
    R42(d2, e2, a2, b2, c2, w12, 9);
    R41(c1, d1, e1, a1, b1, w7, 5);
    R42(c2, d2, e2, a2, b2, w2, 12);
    R41(b1, c1, d1, e1, a1, w15, 6);
    R42(b2, c2, d2, e2, a2, w13, 9);
    R41(a1, b1, c1, d1, e1, w14, 8);
    R42(a2, b2, c2, d2, e2, w9, 12);
    R41(e1, a1, b1, c1, d1, w5, 6);
    R42(e2, a2, b2, c2, d2, w7, 5);
    R41(d1, e1, a1, b1, c1, w6, 5);
    R42(d2, e2, a2, b2, c2, w10, 15);
    R41(c1, d1, e1, a1, b1, w2, 12);
    R42(c2, d2, e2, a2, b2, w14, 8);

    R51(b1, c1, d1, e1, a1, w4, 9);
    R52(b2, c2, d2, e2, a2, w12, 8);
    R51(a1, b1, c1, d1, e1, w0, 15);
    R52(a2, b2, c2, d2, e2, w15, 5);
    R51(e1, a1, b1, c1, d1, w5, 5);
    R52(e2, a2, b2, c2, d2, w10, 12);
    R51(d1, e1, a1, b1, c1, w9, 11);
    R52(d2, e2, a2, b2, c2, w4, 9);
    R51(c1, d1, e1, a1, b1, w7, 6);
    R52(c2, d2, e2, a2, b2, w1, 12);
    R51(b1, c1, d1, e1, a1, w12, 8);
    R52(b2, c2, d2, e2, a2, w5, 5);
    R51(a1, b1, c1, d1, e1, w2, 13);
    R52(a2, b2, c2, d2, e2, w8, 14);
    R51(e1, a1, b1, c1, d1, w10, 12);
    R52(e2, a2, b2, c2, d2, w7, 6);
    R51(d1, e1, a1, b1, c1, w14, 5);
    R52(d2, e2, a2, b2, c2, w6, 8);
    R51(c1, d1, e1, a1, b1, w1, 12);
    R52(c2, d2, e2, a2, b2, w2, 13);
    R51(b1, c1, d1, e1, a1, w3, 13);
    R52(b2, c2, d2, e2, a2, w13, 6);
    R51(a1, b1, c1, d1, e1, w8, 14);
    R52(a2, b2, c2, d2, e2, w14, 5);
    R51(e1, a1, b1, c1, d1, w11, 11);
    R52(e2, a2, b2, c2, d2, w0, 15);
    R51(d1, e1, a1, b1, c1, w6, 8);
    R52(d2, e2, a2, b2, c2, w3, 13);
    R51(c1, d1, e1, a1, b1, w15, 5);
    R52(c2, d2, e2, a2, b2, w9, 11);
    R51(b1, c1, d1, e1, a1, w13, 6);
    R52(b2, c2, d2, e2, a2, w11, 11);

    __m256i tmp = _mm256_set1_epi32(0xEFCDAB89ul);
    Write8(out0, out1, out2, out3, out4, out5, out6, out7, _mm256_add_epi32(_mm256_add_epi32(c1, d2), tmp), 0);
    tmp = _mm256_set1_epi32(0x98BADCFEul);
    Write8(out0, out1, out2, out3, out4, out5, out6, out7, _mm256_add_epi32(_mm256_add_epi32(d1, e2), tmp), 4);
    tmp = _mm256_set1_epi32(0x10325476ul);
    Write8(out0, out1, out2, out3, out4, out5, out6, out7, _mm256_add_epi32(_mm256_add_epi32(e1, a2), tmp), 8);
    tmp = _mm256_set1_epi32(0xC3D2E1F0ul);
    Write8(out0, out1, out2, out3, out4, out5, out6, out7, _mm256_add_epi32(_mm256_add_epi32(a1, b2), tmp), 12);
    tmp = _mm256_set1_epi32(0x67452301ul);
    Write8(out0, out1, out2, out3, out4, out5, out6, out7, _mm256_add_epi32(_mm256_add_epi32(b1, c2), tmp), 16);
}

}


// 4-way SSE SHA256, based on tcatm's code in Bitcoin 0.3.10
namespace sha256_8way {
namespace {

static const uint32_t sha256_consts[] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, /*  0 */
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, /*  8 */
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, /* 16 */
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, /* 24 */
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, /* 32 */
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, /* 40 */
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, /* 48 */
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, /* 56 */
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

inline __m256i Ch(const __m256i b, const __m256i c, const __m256i d) {
    return _mm256_xor_si256(_mm256_and_si256(b,c),_mm256_andnot_si256(b,d));
}

inline __m256i Maj(const __m256i b, const __m256i c, const __m256i d) {
    return _mm256_xor_si256(_mm256_xor_si256(_mm256_and_si256(b,c),_mm256_and_si256(b,d)),_mm256_and_si256(c,d));
}

inline __attribute__((always_inline)) __m256i  ROTR(__m256i x, const int n) {
    return _mm256_or_si256(_mm256_srli_epi32(x, n),_mm256_slli_epi32(x, 32 - n));
}

inline  __attribute__((always_inline))  __m256i SHR(__m256i x, const int n) {
    return _mm256_srli_epi32(x, n);
}

}
/* SHA256 Functions */
#define BIGSIGMA0_256(x)    (_mm256_xor_si256(_mm256_xor_si256(ROTR((x), 2),ROTR((x), 13)),ROTR((x), 22)))
#define BIGSIGMA1_256(x)    (_mm256_xor_si256(_mm256_xor_si256(ROTR((x), 6),ROTR((x), 11)),ROTR((x), 25)))


#define SIGMA0_256(x)       (_mm256_xor_si256(_mm256_xor_si256(ROTR((x), 7),ROTR((x), 18)), SHR((x), 3 )))
#define SIGMA1_256(x)       (_mm256_xor_si256(_mm256_xor_si256(ROTR((x),17),ROTR((x), 19)), SHR((x), 10)))

#define add4(x0, x1, x2, x3) _mm256_add_epi32(_mm256_add_epi32(x0, x1),_mm256_add_epi32( x2,x3))
#define add5(x0, x1, x2, x3, x4) _mm256_add_epi32(add4(x0, x1, x2, x3), x4)

#define SHA256ROUND(a, b, c, d, e, f, g, h, i, w)                       \
    T1 = add5(h, BIGSIGMA1_256(e), Ch(e, f, g), _mm256_set1_epi32(sha256_consts[i]), w);   \
    d = _mm256_add_epi32(d, T1);                                           \
    h = _mm256_add_epi32(T1, _mm256_add_epi32(BIGSIGMA0_256(a), Maj(a, b, c)));

__m256i inline Read8(const unsigned char* chunk) {
    return _mm256_set_epi32(ReadBE32(chunk + 0), ReadBE32(chunk + 64), ReadBE32(chunk + 128), ReadBE32(chunk + 192), ReadBE32(chunk + 256), ReadBE32(chunk + 320), ReadBE32(chunk + 384), ReadBE32(chunk + 448));
}

void inline __attribute__((always_inline)) Write8(unsigned char* out1, unsigned char* out2, unsigned char* out3, unsigned char* out4, unsigned char* out5, unsigned char* out6, unsigned char* out7, unsigned char* out8, __m256i v, size_t offset) {
    union { uint32_t ret[8]; __m256i x; } box;
    box.x = v;
    WriteBE32(out1 + offset, box.ret[0]);
    WriteBE32(out2 + offset, box.ret[1]);
    WriteBE32(out3 + offset, box.ret[2]);
    WriteBE32(out4 + offset, box.ret[3]);
    WriteBE32(out5 + offset, box.ret[4]);
    WriteBE32(out6 + offset, box.ret[5]);
    WriteBE32(out7 + offset, box.ret[6]);
    WriteBE32(out8 + offset, box.ret[7]);
}

void Transform(unsigned char* out1, unsigned char* out2, unsigned char* out3, unsigned char* out4, unsigned char* out5, unsigned char* out6, unsigned char* out7, unsigned char* out8, const unsigned char* chunk) {
    __m256i a = _mm256_set1_epi32(0x6a09e667ul);
    __m256i b = _mm256_set1_epi32(0xbb67ae85ul);
    __m256i c = _mm256_set1_epi32(0x3c6ef372ul);
    __m256i d = _mm256_set1_epi32(0xa54ff53aul);
    __m256i e = _mm256_set1_epi32(0x510e527ful);
    __m256i f = _mm256_set1_epi32(0x9b05688cul);
    __m256i g = _mm256_set1_epi32(0x1f83d9abul);
    __m256i h = _mm256_set1_epi32(0x5be0cd19ul);
    __m256i T1;

    __m256i w0 = Read8(chunk);
    SHA256ROUND(a, b, c, d, e, f, g, h, 0, w0);
    __m256i w1 = Read8(chunk + 4);
    SHA256ROUND(h, a, b, c, d, e, f, g, 1, w1);
    __m256i w2 = Read8(chunk + 8);
    SHA256ROUND(g, h, a, b, c, d, e, f, 2, w2);
    __m256i w3 = Read8(chunk + 12);
    SHA256ROUND(f, g, h, a, b, c, d, e, 3, w3);
    __m256i w4 = Read8(chunk + 16);
    SHA256ROUND(e, f, g, h, a, b, c, d, 4, w4);
    __m256i w5 = Read8(chunk + 20);
    SHA256ROUND(d, e, f, g, h, a, b, c, 5, w5);
    __m256i w6 = Read8(chunk + 24);
    SHA256ROUND(c, d, e, f, g, h, a, b, 6, w6);
    __m256i w7 = Read8(chunk + 28);
    SHA256ROUND(b, c, d, e, f, g, h, a, 7, w7);
    __m256i w8 = Read8(chunk + 32);
    SHA256ROUND(a, b, c, d, e, f, g, h, 8, w8);
    __m256i w9 = Read8(chunk + 36);
    SHA256ROUND(h, a, b, c, d, e, f, g, 9, w9);
    __m256i w10 = Read8(chunk + 40);
    SHA256ROUND(g, h, a, b, c, d, e, f, 10, w10);
    __m256i w11 = Read8(chunk + 44);
    SHA256ROUND(f, g, h, a, b, c, d, e, 11, w11);
    __m256i w12 = Read8(chunk + 48);
    SHA256ROUND(e, f, g, h, a, b, c, d, 12, w12);
    __m256i w13 = Read8(chunk + 52);
    SHA256ROUND(d, e, f, g, h, a, b, c, 13, w13);
    __m256i w14 = Read8(chunk + 56);
    SHA256ROUND(c, d, e, f, g, h, a, b, 14, w14);
    __m256i w15 = Read8(chunk + 60);
    SHA256ROUND(b, c, d, e, f, g, h, a, 15, w15);

    w0 = add4(SIGMA1_256(w14), w9, SIGMA0_256(w1), w0);
    SHA256ROUND(a, b, c, d, e, f, g, h, 16, w0);
    w1 = add4(SIGMA1_256(w15), w10, SIGMA0_256(w2), w1);
    SHA256ROUND(h, a, b, c, d, e, f, g, 17, w1);
    w2 = add4(SIGMA1_256(w0), w11, SIGMA0_256(w3), w2);
    SHA256ROUND(g, h, a, b, c, d, e, f, 18, w2);
    w3 = add4(SIGMA1_256(w1), w12, SIGMA0_256(w4), w3);
    SHA256ROUND(f, g, h, a, b, c, d, e, 19, w3);
    w4 = add4(SIGMA1_256(w2), w13, SIGMA0_256(w5), w4);
    SHA256ROUND(e, f, g, h, a, b, c, d, 20, w4);
    w5 = add4(SIGMA1_256(w3), w14, SIGMA0_256(w6), w5);
    SHA256ROUND(d, e, f, g, h, a, b, c, 21, w5);
    w6 = add4(SIGMA1_256(w4), w15, SIGMA0_256(w7), w6);
    SHA256ROUND(c, d, e, f, g, h, a, b, 22, w6);
    w7 = add4(SIGMA1_256(w5), w0, SIGMA0_256(w8), w7);
    SHA256ROUND(b, c, d, e, f, g, h, a, 23, w7);
    w8 = add4(SIGMA1_256(w6), w1, SIGMA0_256(w9), w8);
    SHA256ROUND(a, b, c, d, e, f, g, h, 24, w8);
    w9 = add4(SIGMA1_256(w7), w2, SIGMA0_256(w10), w9);
    SHA256ROUND(h, a, b, c, d, e, f, g, 25, w9);
    w10 = add4(SIGMA1_256(w8), w3, SIGMA0_256(w11), w10);
    SHA256ROUND(g, h, a, b, c, d, e, f, 26, w10);
    w11 = add4(SIGMA1_256(w9), w4, SIGMA0_256(w12), w11);
    SHA256ROUND(f, g, h, a, b, c, d, e, 27, w11);
    w12 = add4(SIGMA1_256(w10), w5, SIGMA0_256(w13), w12);
    SHA256ROUND(e, f, g, h, a, b, c, d, 28, w12);
    w13 = add4(SIGMA1_256(w11), w6, SIGMA0_256(w14), w13);
    SHA256ROUND(d, e, f, g, h, a, b, c, 29, w13);
    w14 = add4(SIGMA1_256(w12), w7, SIGMA0_256(w15), w14);
    SHA256ROUND(c, d, e, f, g, h, a, b, 30, w14);
    w15 = add4(SIGMA1_256(w13), w8, SIGMA0_256(w0), w15);
    SHA256ROUND(b, c, d, e, f, g, h, a, 31, w15);

    w0 = add4(SIGMA1_256(w14), w9, SIGMA0_256(w1), w0);
    SHA256ROUND(a, b, c, d, e, f, g, h, 32, w0);
    w1 = add4(SIGMA1_256(w15), w10, SIGMA0_256(w2), w1);
    SHA256ROUND(h, a, b, c, d, e, f, g, 33, w1);
    w2 = add4(SIGMA1_256(w0), w11, SIGMA0_256(w3), w2);
    SHA256ROUND(g, h, a, b, c, d, e, f, 34, w2);
    w3 = add4(SIGMA1_256(w1), w12, SIGMA0_256(w4), w3);
    SHA256ROUND(f, g, h, a, b, c, d, e, 35, w3);
    w4 = add4(SIGMA1_256(w2), w13, SIGMA0_256(w5), w4);
    SHA256ROUND(e, f, g, h, a, b, c, d, 36, w4);
    w5 = add4(SIGMA1_256(w3), w14, SIGMA0_256(w6), w5);
    SHA256ROUND(d, e, f, g, h, a, b, c, 37, w5);
    w6 = add4(SIGMA1_256(w4), w15, SIGMA0_256(w7), w6);
    SHA256ROUND(c, d, e, f, g, h, a, b, 38, w6);
    w7 = add4(SIGMA1_256(w5), w0, SIGMA0_256(w8), w7);
    SHA256ROUND(b, c, d, e, f, g, h, a, 39, w7);
    w8 = add4(SIGMA1_256(w6), w1, SIGMA0_256(w9), w8);
    SHA256ROUND(a, b, c, d, e, f, g, h, 40, w8);
    w9 = add4(SIGMA1_256(w7), w2, SIGMA0_256(w10), w9);
    SHA256ROUND(h, a, b, c, d, e, f, g, 41, w9);
    w10 = add4(SIGMA1_256(w8), w3, SIGMA0_256(w11), w10);
    SHA256ROUND(g, h, a, b, c, d, e, f, 42, w10);
    w11 = add4(SIGMA1_256(w9), w4, SIGMA0_256(w12), w11);
    SHA256ROUND(f, g, h, a, b, c, d, e, 43, w11);
    w12 = add4(SIGMA1_256(w10), w5, SIGMA0_256(w13), w12);
    SHA256ROUND(e, f, g, h, a, b, c, d, 44, w12);
    w13 = add4(SIGMA1_256(w11), w6, SIGMA0_256(w14), w13);
    SHA256ROUND(d, e, f, g, h, a, b, c, 45, w13);
    w14 = add4(SIGMA1_256(w12), w7, SIGMA0_256(w15), w14);
    SHA256ROUND(c, d, e, f, g, h, a, b, 46, w14);
    w15 = add4(SIGMA1_256(w13), w8, SIGMA0_256(w0), w15);
    SHA256ROUND(b, c, d, e, f, g, h, a, 47, w15);

    w0 = add4(SIGMA1_256(w14), w9, SIGMA0_256(w1), w0);
    SHA256ROUND(a, b, c, d, e, f, g, h, 48, w0);
    w1 = add4(SIGMA1_256(w15), w10, SIGMA0_256(w2), w1);
    SHA256ROUND(h, a, b, c, d, e, f, g, 49, w1);
    w2 = add4(SIGMA1_256(w0), w11, SIGMA0_256(w3), w2);
    SHA256ROUND(g, h, a, b, c, d, e, f, 50, w2);
    w3 = add4(SIGMA1_256(w1), w12, SIGMA0_256(w4), w3);
    SHA256ROUND(f, g, h, a, b, c, d, e, 51, w3);
    w4 = add4(SIGMA1_256(w2), w13, SIGMA0_256(w5), w4);
    SHA256ROUND(e, f, g, h, a, b, c, d, 52, w4);
    w5 = add4(SIGMA1_256(w3), w14, SIGMA0_256(w6), w5);
    SHA256ROUND(d, e, f, g, h, a, b, c, 53, w5);
    w6 = add4(SIGMA1_256(w4), w15, SIGMA0_256(w7), w6);
    SHA256ROUND(c, d, e, f, g, h, a, b, 54, w6);
    w7 = add4(SIGMA1_256(w5), w0, SIGMA0_256(w8), w7);
    SHA256ROUND(b, c, d, e, f, g, h, a, 55, w7);
    w8 = add4(SIGMA1_256(w6), w1, SIGMA0_256(w9), w8);
    SHA256ROUND(a, b, c, d, e, f, g, h, 56, w8);
    w9 = add4(SIGMA1_256(w7), w2, SIGMA0_256(w10), w9);
    SHA256ROUND(h, a, b, c, d, e, f, g, 57, w9);
    w10 = add4(SIGMA1_256(w8), w3, SIGMA0_256(w11), w10);
    SHA256ROUND(g, h, a, b, c, d, e, f, 58, w10);
    w11 = add4(SIGMA1_256(w9), w4, SIGMA0_256(w12), w11);
    SHA256ROUND(f, g, h, a, b, c, d, e, 59, w11);
    w12 = add4(SIGMA1_256(w10), w5, SIGMA0_256(w13), w12);
    SHA256ROUND(e, f, g, h, a, b, c, d, 60, w12);
    w13 = add4(SIGMA1_256(w11), w6, SIGMA0_256(w14), w13);
    SHA256ROUND(d, e, f, g, h, a, b, c, 61, w13);
    w14 = add4(SIGMA1_256(w12), w7, SIGMA0_256(w15), w14);
    SHA256ROUND(c, d, e, f, g, h, a, b, 62, w14);
    w15 = add4(SIGMA1_256(w13), w8, SIGMA0_256(w0), w15);
    SHA256ROUND(b, c, d, e, f, g, h, a, 63, w15);

    __m256i tmp = _mm256_set1_epi32(0x6a09e667ul);
    Write8(out1, out2, out3, out4, out5, out6, out7, out8, _mm256_add_epi32(a, tmp), 0);
    tmp = _mm256_set1_epi32(0xbb67ae85ul);
    Write8(out1, out2, out3, out4, out5, out6, out7, out8, _mm256_add_epi32(b, tmp), 4);
    tmp = _mm256_set1_epi32(0x3c6ef372ul);
    Write8(out1, out2, out3, out4, out5, out6, out7, out8, _mm256_add_epi32(c, tmp), 8);
    tmp = _mm256_set1_epi32(0xa54ff53aul);
    Write8(out1, out2, out3, out4, out5, out6, out7, out8, _mm256_add_epi32(d, tmp), 12);
    tmp = _mm256_set1_epi32(0x510e527ful);
    Write8(out1, out2, out3, out4, out5, out6, out7, out8, _mm256_add_epi32(e, tmp), 16);
    tmp = _mm256_set1_epi32(0x9b05688cul);
    Write8(out1, out2, out3, out4, out5, out6, out7, out8, _mm256_add_epi32(f, tmp), 20);
    tmp = _mm256_set1_epi32(0x1f83d9abul);
    Write8(out1, out2, out3, out4, out5, out6, out7, out8, _mm256_add_epi32(g, tmp), 24);
    tmp = _mm256_set1_epi32(0x5be0cd19ul);
    Write8(out1, out2, out3, out4, out5, out6, out7, out8, _mm256_add_epi32(h, tmp), 28);
}


}

namespace sha256 {

namespace {

uint32_t inline Ch(uint32_t x, uint32_t y, uint32_t z) { return z ^ (x & (y ^ z)); }
uint32_t inline Maj(uint32_t x, uint32_t y, uint32_t z) { return (x & y) | (z & (x | y)); }
uint32_t inline Sigma0(uint32_t x) { return (x >> 2 | x << 30) ^ (x >> 13 | x << 19) ^ (x >> 22 | x << 10); }
uint32_t inline Sigma1(uint32_t x) { return (x >> 6 | x << 26) ^ (x >> 11 | x << 21) ^ (x >> 25 | x << 7); }
uint32_t inline sigma0(uint32_t x) { return (x >> 7 | x << 25) ^ (x >> 18 | x << 14) ^ (x >> 3); }
uint32_t inline sigma1(uint32_t x) { return (x >> 17 | x << 15) ^ (x >> 19 | x << 13) ^ (x >> 10); }

/** One round of SHA-256. */
void inline Round(uint32_t a, uint32_t b, uint32_t c, uint32_t& d, uint32_t e, uint32_t f, uint32_t g, uint32_t& h, uint32_t k, uint32_t w)
{
    uint32_t t1 = h + Sigma1(e) + Ch(e, f, g) + k + w;
    uint32_t t2 = Sigma0(a) + Maj(a, b, c);
    d += t1;
    h = t1 + t2;
}

}

void Transform(unsigned char* out, const unsigned char* chunk)
{
    uint32_t a = 0x6a09e667ul, b = 0xbb67ae85ul, c = 0x3c6ef372ul, d = 0xa54ff53aul, e = 0x510e527ful, f = 0x9b05688cul, g = 0x1f83d9abul, h = 0x5be0cd19ul;
    uint32_t w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15;

    Round(a, b, c, d, e, f, g, h, 0x428a2f98, w0 = ReadBE32(chunk + 0));
    Round(h, a, b, c, d, e, f, g, 0x71374491, w1 = ReadBE32(chunk + 4));
    Round(g, h, a, b, c, d, e, f, 0xb5c0fbcf, w2 = ReadBE32(chunk + 8));
    Round(f, g, h, a, b, c, d, e, 0xe9b5dba5, w3 = ReadBE32(chunk + 12));
    Round(e, f, g, h, a, b, c, d, 0x3956c25b, w4 = ReadBE32(chunk + 16));
    Round(d, e, f, g, h, a, b, c, 0x59f111f1, w5 = ReadBE32(chunk + 20));
    Round(c, d, e, f, g, h, a, b, 0x923f82a4, w6 = ReadBE32(chunk + 24));
    Round(b, c, d, e, f, g, h, a, 0xab1c5ed5, w7 = ReadBE32(chunk + 28));
    Round(a, b, c, d, e, f, g, h, 0xd807aa98, w8 = ReadBE32(chunk + 32));
    Round(h, a, b, c, d, e, f, g, 0x12835b01, w9 = ReadBE32(chunk + 36));
    Round(g, h, a, b, c, d, e, f, 0x243185be, w10 = ReadBE32(chunk + 40));
    Round(f, g, h, a, b, c, d, e, 0x550c7dc3, w11 = ReadBE32(chunk + 44));
    Round(e, f, g, h, a, b, c, d, 0x72be5d74, w12 = ReadBE32(chunk + 48));
    Round(d, e, f, g, h, a, b, c, 0x80deb1fe, w13 = ReadBE32(chunk + 52));
    Round(c, d, e, f, g, h, a, b, 0x9bdc06a7, w14 = ReadBE32(chunk + 56));
    Round(b, c, d, e, f, g, h, a, 0xc19bf174, w15 = ReadBE32(chunk + 60));

    Round(a, b, c, d, e, f, g, h, 0xe49b69c1, w0 += sigma1(w14) + w9 + sigma0(w1));
    Round(h, a, b, c, d, e, f, g, 0xefbe4786, w1 += sigma1(w15) + w10 + sigma0(w2));
    Round(g, h, a, b, c, d, e, f, 0x0fc19dc6, w2 += sigma1(w0) + w11 + sigma0(w3));
    Round(f, g, h, a, b, c, d, e, 0x240ca1cc, w3 += sigma1(w1) + w12 + sigma0(w4));
    Round(e, f, g, h, a, b, c, d, 0x2de92c6f, w4 += sigma1(w2) + w13 + sigma0(w5));
    Round(d, e, f, g, h, a, b, c, 0x4a7484aa, w5 += sigma1(w3) + w14 + sigma0(w6));
    Round(c, d, e, f, g, h, a, b, 0x5cb0a9dc, w6 += sigma1(w4) + w15 + sigma0(w7));
    Round(b, c, d, e, f, g, h, a, 0x76f988da, w7 += sigma1(w5) + w0 + sigma0(w8));
    Round(a, b, c, d, e, f, g, h, 0x983e5152, w8 += sigma1(w6) + w1 + sigma0(w9));
    Round(h, a, b, c, d, e, f, g, 0xa831c66d, w9 += sigma1(w7) + w2 + sigma0(w10));
    Round(g, h, a, b, c, d, e, f, 0xb00327c8, w10 += sigma1(w8) + w3 + sigma0(w11));
    Round(f, g, h, a, b, c, d, e, 0xbf597fc7, w11 += sigma1(w9) + w4 + sigma0(w12));
    Round(e, f, g, h, a, b, c, d, 0xc6e00bf3, w12 += sigma1(w10) + w5 + sigma0(w13));
    Round(d, e, f, g, h, a, b, c, 0xd5a79147, w13 += sigma1(w11) + w6 + sigma0(w14));
    Round(c, d, e, f, g, h, a, b, 0x06ca6351, w14 += sigma1(w12) + w7 + sigma0(w15));
    Round(b, c, d, e, f, g, h, a, 0x14292967, w15 += sigma1(w13) + w8 + sigma0(w0));

    Round(a, b, c, d, e, f, g, h, 0x27b70a85, w0 += sigma1(w14) + w9 + sigma0(w1));
    Round(h, a, b, c, d, e, f, g, 0x2e1b2138, w1 += sigma1(w15) + w10 + sigma0(w2));
    Round(g, h, a, b, c, d, e, f, 0x4d2c6dfc, w2 += sigma1(w0) + w11 + sigma0(w3));
    Round(f, g, h, a, b, c, d, e, 0x53380d13, w3 += sigma1(w1) + w12 + sigma0(w4));
    Round(e, f, g, h, a, b, c, d, 0x650a7354, w4 += sigma1(w2) + w13 + sigma0(w5));
    Round(d, e, f, g, h, a, b, c, 0x766a0abb, w5 += sigma1(w3) + w14 + sigma0(w6));
    Round(c, d, e, f, g, h, a, b, 0x81c2c92e, w6 += sigma1(w4) + w15 + sigma0(w7));
    Round(b, c, d, e, f, g, h, a, 0x92722c85, w7 += sigma1(w5) + w0 + sigma0(w8));
    Round(a, b, c, d, e, f, g, h, 0xa2bfe8a1, w8 += sigma1(w6) + w1 + sigma0(w9));
    Round(h, a, b, c, d, e, f, g, 0xa81a664b, w9 += sigma1(w7) + w2 + sigma0(w10));
    Round(g, h, a, b, c, d, e, f, 0xc24b8b70, w10 += sigma1(w8) + w3 + sigma0(w11));
    Round(f, g, h, a, b, c, d, e, 0xc76c51a3, w11 += sigma1(w9) + w4 + sigma0(w12));
    Round(e, f, g, h, a, b, c, d, 0xd192e819, w12 += sigma1(w10) + w5 + sigma0(w13));
    Round(d, e, f, g, h, a, b, c, 0xd6990624, w13 += sigma1(w11) + w6 + sigma0(w14));
    Round(c, d, e, f, g, h, a, b, 0xf40e3585, w14 += sigma1(w12) + w7 + sigma0(w15));
    Round(b, c, d, e, f, g, h, a, 0x106aa070, w15 += sigma1(w13) + w8 + sigma0(w0));

    Round(a, b, c, d, e, f, g, h, 0x19a4c116, w0 += sigma1(w14) + w9 + sigma0(w1));
    Round(h, a, b, c, d, e, f, g, 0x1e376c08, w1 += sigma1(w15) + w10 + sigma0(w2));
    Round(g, h, a, b, c, d, e, f, 0x2748774c, w2 += sigma1(w0) + w11 + sigma0(w3));
    Round(f, g, h, a, b, c, d, e, 0x34b0bcb5, w3 += sigma1(w1) + w12 + sigma0(w4));
    Round(e, f, g, h, a, b, c, d, 0x391c0cb3, w4 += sigma1(w2) + w13 + sigma0(w5));
    Round(d, e, f, g, h, a, b, c, 0x4ed8aa4a, w5 += sigma1(w3) + w14 + sigma0(w6));
    Round(c, d, e, f, g, h, a, b, 0x5b9cca4f, w6 += sigma1(w4) + w15 + sigma0(w7));
    Round(b, c, d, e, f, g, h, a, 0x682e6ff3, w7 += sigma1(w5) + w0 + sigma0(w8));
    Round(a, b, c, d, e, f, g, h, 0x748f82ee, w8 += sigma1(w6) + w1 + sigma0(w9));
    Round(h, a, b, c, d, e, f, g, 0x78a5636f, w9 += sigma1(w7) + w2 + sigma0(w10));
    Round(g, h, a, b, c, d, e, f, 0x84c87814, w10 += sigma1(w8) + w3 + sigma0(w11));
    Round(f, g, h, a, b, c, d, e, 0x8cc70208, w11 += sigma1(w9) + w4 + sigma0(w12));
    Round(e, f, g, h, a, b, c, d, 0x90befffa, w12 += sigma1(w10) + w5 + sigma0(w13));
    Round(d, e, f, g, h, a, b, c, 0xa4506ceb, w13 += sigma1(w11) + w6 + sigma0(w14));
    Round(c, d, e, f, g, h, a, b, 0xbef9a3f7, w14 + sigma1(w12) + w7 + sigma0(w15));
    Round(b, c, d, e, f, g, h, a, 0xc67178f2, w15 + sigma1(w13) + w8 + sigma0(w0));

    WriteBE32(out, 0x6a09e667ul + a);
    WriteBE32(out + 4, 0xbb67ae85ul + b);
    WriteBE32(out + 8, 0x3c6ef372ul + c);
    WriteBE32(out + 12, 0xa54ff53aul + d);
    WriteBE32(out + 16, 0x510e527ful + e);
    WriteBE32(out + 20, 0x9b05688cul + f);
    WriteBE32(out + 24, 0x1f83d9abul + g);
    WriteBE32(out + 28, 0x5be0cd19ul + h);
}

}
