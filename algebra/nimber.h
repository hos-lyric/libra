#ifndef LIBRA_ALGEBRA_NIMBER_H_
#define LIBRA_ALGEBRA_NIMBER_H_

#include <string.h>

////////////////////////////////////////////////////////////////////////////////
namespace nim {

using u16 = unsigned short;
using u32 = unsigned;
using u64 = unsigned long long;

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

constexpr u16 G16 = 10279U;
u16 buf[4 * ((1 << 16) - 1) + 26];
u16 *exp = buf + (2 * ((1 << 16) - 1) + 18), *exp3 = exp + 3, *exp6 = exp + 6;
int log[1 << 16];

struct Preparator {
  Preparator() {
    exp[0] = 1;
    for (int i = 1; i < (1 << 16) - 1; ++i) exp[i] = mulSlow<16>(exp[i - 1], G16);
    log[0] = -(((1 << 16) - 1) + 9);
    for (int i = 0; i < (1 << 16) - 1; ++i) log[exp[i]] = i;
    memcpy(exp + ((1 << 16) - 1), exp, ((1 << 16) - 1) * sizeof(u16));
    memcpy(exp + 2 * ((1 << 16) - 1), exp, 8 * sizeof(u16));
  }
} preparator;

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
  u64 aa = a >> 16, aaa = a >> 32;
  u64 bb = b >> 16, bbb = b >> 32;
  const u16 a0 = a, a1 = aa, a2 = aaa, a3 = a >> 48;
  const u16 b0 = b, b1 = bb, b2 = bbb, b3 = b >> 48;
  aa ^= a; aaa ^= a;
  bb ^= b; bbb ^= b;
  const u16 a01 = aa, a23 = aa >> 32, a02 = aaa, a13 = aaa >> 16;
  const u16 b01 = bb, b23 = bb >> 32, b02 = bbb, b13 = bbb >> 16;
  const u16 a0123 = a01 ^ a23;
  const u16 b0123 = b01 ^ b23;
  const u16 a0b0 = mul(a0, b0), a23b23 = mul(a23, b23), a02b02 = mul(a02, b02);
  const u32 c = (a0b0 ^ exp3[log[a1] + log[b1]]) | (u32)(a0b0 ^ mul(a01, b01)) << 16;
  return (c ^ (exp6[log[mul(a2, b2) ^ a23b23]] | (u32)exp3[log[exp3[log[a3] + log[b3]] ^ a23b23]] << 16))
      | (u64)(c ^ ((a02b02 ^ exp3[log[a13] + log[b13]]) | (u32)(a02b02 ^ mul(a0123, b0123)) << 16)) << 32;
}

}  // namespace nim
////////////////////////////////////////////////////////////////////////////////

#endif  // LIBRA_ALGEBRA_NIMBER_H_
