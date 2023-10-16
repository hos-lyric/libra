#ifndef LIBRA_ALGEBRA_NIMBER_H_
#define LIBRA_ALGEBRA_NIMBER_H_

#include <assert.h>

////////////////////////////////////////////////////////////////////////////////
namespace nim {
using u16 = unsigned short;
using u32 = unsigned;
using u64 = unsigned long long;

// G16: primitive root in F_(2^16)
// G16\^3 = 2^15
constexpr u16 G16 = 10279U;
u16 expBuffer[4 * (1 << 16) + 4];
u16 *exp = expBuffer + (2 * (1 << 16) + 4), *exp3 = exp + 3, *exp6 = exp + 6;
int log[1 << 16];
u64 tabSq[4][1 << 16], tabSqrt[4][1 << 16], tabSolveQuad1[4][1 << 16];

// L: power of 2
// (a0 + 2^l a1) \* (b0 + 2^l b1)
// = (a0\*b0 \+ 2^(l-1)\*a1\*b1) + 2^l (a0\*b1 \+ a1\*b0 \+ a1\*b1)
template <int L> inline u64 mulSlow(u64 a, u64 b) {
  static constexpr int l = L >> 1;
  const u64 a0 = a & ((1ULL << l) - 1), a1 = a >> l;
  const u64 b0 = b & ((1ULL << l) - 1), b1 = b >> l;
  const u64 a0b0 = mulSlow<l>(a0, b0);
  return (a0b0 ^ mulSlow<l>(1ULL << (l - 1), mulSlow<l>(a1, b1)))
      | (a0b0 ^ mulSlow<l>(a0 ^ a1, b0 ^ b1)) << l;
}
template <> inline u64 mulSlow<1>(u64 a, u64 b) {
  return a & b;
}

// 2^31 \* a
inline u32 mul31(u32 a) {
  const u16 a0 = a, a1 = a >> 16;
  const u16 a01 = a0 ^ a1;
  return exp6[log[a1]] | (u32)exp3[log[a01]] << 16;
}

inline u16 mul(u16 a, u16 b) {
  return exp[log[a] + log[b]];
}
inline u32 mul(u32 a, u32 b) {
  const u16 a0 = a, a1 = a >> 16;
  const u16 b0 = b, b1 = b >> 16;
  const u16 a01 = a0 ^ a1;
  const u16 b01 = b0 ^ b1;
  const u16 a0b0 = mul(a0, b0);
  return (a0b0 ^ exp3[log[a1] + log[b1]]) | (u32)(a0b0 ^ mul(a01, b01)) << 16;
}
inline u64 mul(u64 a, u64 b) {
  const u32 a0 = a, a1 = a >> 32;
  const u32 b0 = b, b1 = b >> 32;
  const u32 a01 = a0 ^ a1;
  const u32 b01 = b0 ^ b1;
  const u32 a0b0 = mul(a0, b0);
  return (a0b0 ^ mul31(mul(a1, b1))) | (u64)(a0b0 ^ mul(a01, b01)) << 32;
}

inline u16 sq(u16 a) {
  return tabSq[0][a];
}
inline u32 sq(u32 a) {
  const u16 a0 = a, a1 = a >> 16;
  return tabSq[0][a0] ^ tabSq[1][a1];
}
inline u64 sq(u64 a) {
  const u16 a0 = a, a1 = a >> 16, a2 = a >> 32, a3 = a >> 48;
  return tabSq[0][a0] ^ tabSq[1][a1] ^ tabSq[2][a2] ^ tabSq[3][a3];
}

inline u16 sqrt(u16 a) {
  return tabSqrt[0][a];
}
inline u32 sqrt(u32 a) {
  const u16 a0 = a, a1 = a >> 16;
  return tabSqrt[0][a0] ^ tabSqrt[1][a1];
}
inline u64 sqrt(u64 a) {
  const u16 a0 = a, a1 = a >> 16, a2 = a >> 32, a3 = a >> 48;
  return tabSqrt[0][a0] ^ tabSqrt[1][a1] ^ tabSqrt[2][a2] ^ tabSqrt[3][a3];
}

// (a0 + 2^l a1) \* (b0 + 2^l b1) = 1
// <=> [ a0  2^(l-1)\*a1 ] \* [ b0 ] = [ 1 ]
//     [ a1  a0\+a1      ]    [ b1 ]   [ 0 ]
inline u16 inv(u16 a) {
  assert(a);
  return exp[((1 << 16) - 1) - log[a]];
}
inline u32 inv(u32 a) {
  assert(a);
  const u16 a0 = a, a1 = a >> 16;
  const u16 a01 = a0 ^ a1;
  const u16 d = inv((u16)(mul(a0, a01) ^ exp3[log[a1] + log[a1]]));
  return mul(d, a01) | (u32)mul(d, a1) << 16;
}
inline u64 inv(u64 a) {
  assert(a);
  const u32 a0 = a, a1 = a >> 32;
  const u32 a01 = a0 ^ a1;
  const u32 d = inv(mul(a0, a01) ^ mul31(sq(a1)));
  return mul(d, a01) | (u64)mul(d, a1) << 32;
}

// f(x) := x\^2 \+ x
// bsr(x\^2) = bsr(x)
// f: {even in [0, 2^L)} -> [0, 2^(L-1)): linear isom.
// f(x0 + 2^l x1) = (f(x0) \+ 2^(l-1)\*x1\^2) + 2^l f(x1)
template <int L> inline u64 solveQuad1Slow(u64 a) {
  static constexpr int l = L >> 1;
  assert(!(a >> (L - 1)));
  const u64 a0 = a & ((1ULL << l) - 1), a1 = a >> l;
  const u64 x1 = solveQuad1Slow<l>(a1);
  const u64 b0 = a0 ^ mul(1ULL << (l - 1), sq(x1));
  const u64 s = b0 >> (l - 1);
  return solveQuad1Slow<l>(b0 ^ s << (l - 1)) | (x1 ^ s) << l;
}
template <> inline u64 solveQuad1Slow<1>(u64 a) {
  assert(!a);
  return 0;
}

// x\^2 \+ x \+ a = 0
// solutions: x, x \+ 1
inline u64 solveQuad1(u64 a) {
  assert(!(a >> 63));
  const u16 a0 = a, a1 = a >> 16, a2 = a >> 32, a3 = a >> 48;
  return tabSolveQuad1[0][a0] ^ tabSolveQuad1[1][a1] ^ tabSolveQuad1[2][a2] ^ tabSolveQuad1[3][a3];
}

// x\^2 \+ a\*x \+ b = 0
// solutions: x, x \+ a
inline bool isSolvableQuad(u64 a, u64 b) {
  return !(mul(inv(sq(a)), b) >> 63);
}
inline u64 solveQuad(u64 a, u64 b) {
  return a ? mul(a, solveQuad1(mul(inv(sq(a)), b))) : sqrt(b);
}

struct Preparator {
  Preparator() {
    exp[0] = 1;
    for (int i = 1; i < (1 << 16) - 1; ++i) exp[i] = mulSlow<16>(exp[i - 1], G16);
    for (int i = (1 << 16) - 1; i < 2 * (1 << 16); ++i) exp[i] = exp[i - ((1 << 16) - 1)];
    for (int i = 0; i < (1 << 16) - 1; ++i) log[exp[i]] = i;
    log[0] = -(1 << 16) - 2;
    for (int e = 0; e < 64; ++e) {
      const u64 x = mul(1ULL << e, 1ULL << e);
      for (int i = 0; i < 1 << (e & 15); ++i) tabSq[e >> 4][i | 1 << (e & 15)] = tabSq[e >> 4][i] ^ x;
    }
    for (int e = 0; e < 64; ++e) {
      u64 x = 1ULL << e;
      for (int j = 0; j < 63; ++j) x = sq(x);
      for (int i = 0; i < 1 << (e & 15); ++i) tabSqrt[e >> 4][i | 1 << (e & 15)] = tabSqrt[e >> 4][i] ^ x;
    }
    for (int e = 0; e < 63; ++e) {
      const u64 x = solveQuad1Slow<64>(1ULL << e);
      for (int i = 0; i < 1 << (e & 15); ++i) tabSolveQuad1[e >> 4][i | 1 << (e & 15)] = tabSolveQuad1[e >> 4][i] ^ x;
    }
  }
} preparator;
}  // namespace nim
////////////////////////////////////////////////////////////////////////////////

#endif  // LIBRA_ALGEBRA_NIMBER_H_
