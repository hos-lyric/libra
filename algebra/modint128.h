#ifndef LIBRA_ALGEBRA_MODINT128_H_
#define LIBRA_ALGEBRA_MODINT128_H_

#include <assert.h>
#include <iostream>

#include "../other/int128.h"

////////////////////////////////////////////////////////////////////////////////
// floor(a b / 2^128)
inline unsigned __int128 mul128High(unsigned __int128 a, unsigned __int128 b) {
  const unsigned __int128 a0 = static_cast<unsigned long long>(a), a1 = a >> 64;
  const unsigned __int128 b0 = static_cast<unsigned long long>(b), b1 = b >> 64;
  return ((((a0 * b0) >> 64) + static_cast<unsigned long long>(a0 * b1) + static_cast<unsigned long long>(a1 * b0)) >> 64) + ((a0 * b1) >> 64) + ((a1 * b0) >> 64) + a1 * b1;
}

// Hold y := (2^128 x) mod M
template <int ID> struct RMModInt128 {
  static unsigned __int128 M;
  static unsigned __int128 INV_M;  // M^-1 mod 2^128
  static unsigned __int128 TWO256;  // 2^256 mod M
  static void setM(unsigned __int128 m) {
    assert(m & 1); assert(1 <= m); assert(!(m >> 127));
    M = m;
    INV_M = (3 * M) ^ 2;
    for (int i = 0; i < 5; ++i) INV_M *= (2 - M * INV_M);
    TWO256 = (-M) % M;
    for (int i = 0; i < 128; ++i) TWO256 = ((TWO256 <<= 1) >= M) ? (TWO256 - M) : TWO256;
  }
  // (2^-128 a) mod M  (0 <= a < 2^128 m)
  static inline unsigned __int128 reduce(unsigned __int128 a) {
    const unsigned __int128 c = -mul128High(INV_M * a, M);
    return (c >= M) ? (c + M) : c;
  }
  // (2^-128 a b) mod M  (0 <= a b < 2^128 m)
  static inline unsigned __int128 mulReduce(unsigned __int128 a, unsigned __int128 b) {
    const unsigned __int128 c = mul128High(a, b) - mul128High(INV_M * (a * b), M);
    return (c >= M) ? (c + M) : c;
  }

  unsigned __int128 y;
  RMModInt128() : y(0U) {}
  RMModInt128(unsigned x_) : y(mulReduce(TWO256, x_ % M)) {}
  RMModInt128(unsigned long long x_) : y(mulReduce(TWO256, x_ % M)) {}
  RMModInt128(unsigned __int128 x_) : y(mulReduce(TWO256, x_ % M)) {}
  RMModInt128(int x_) : y(mulReduce(TWO256, ((x_ %= static_cast<__int128>(M)) < 0) ? (x_ + static_cast<__int128>(M)) : x_)) {}
  RMModInt128(long long x_) : y(mulReduce(TWO256, ((x_ %= static_cast<__int128>(M)) < 0) ? (x_ + static_cast<__int128>(M)) : x_)) {}
  RMModInt128(__int128 x_) : y(mulReduce(TWO256, ((x_ %= static_cast<__int128>(M)) < 0) ? (x_ + static_cast<__int128>(M)) : x_)) {}
  unsigned __int128 get() const { return reduce(y); }
  RMModInt128 &operator+=(const RMModInt128 &a) { y = ((y += a.y) >= M) ? (y - M) : y; return *this; }
  RMModInt128 &operator-=(const RMModInt128 &a) { y = ((y -= a.y) >= M) ? (y + M) : y; return *this; }
  RMModInt128 &operator*=(const RMModInt128 &a) { y = mulReduce(y, a.y); return *this; }
  RMModInt128 &operator/=(const RMModInt128 &a) { return (*this *= a.inv()); }
  template <class T> RMModInt128 pow(T e) const {
    if (e < 0) return inv().pow(-e);
    for (RMModInt128 a = *this, b = 1U; ; a *= a) { if (e & 1) { b *= a; } if (!(e >>= 1)) { return b; } }
  }
  RMModInt128 inv() const {
    unsigned __int128 a = M, b = reduce(reduce(y)); __int128 u = 0, v = 1;
    for (; b; ) { const unsigned __int128 q = a / b; const unsigned __int128 c = a - q * b; a = b; b = c; const __int128 w = u - static_cast<__int128>(q) * v; u = v; v = w; }
    assert(a == 1U); RMModInt128 r; r.y = u; r.y = (r.y >= M) ? (r.y + M) : r.y; return r;
  }
  RMModInt128 operator+() const { return *this; }
  RMModInt128 operator-() const { RMModInt128 a; a.y = y ? (M - y) : 0U; return a; }
  RMModInt128 operator+(const RMModInt128 &a) const { return (RMModInt128(*this) += a); }
  RMModInt128 operator-(const RMModInt128 &a) const { return (RMModInt128(*this) -= a); }
  RMModInt128 operator*(const RMModInt128 &a) const { return (RMModInt128(*this) *= a); }
  RMModInt128 operator/(const RMModInt128 &a) const { return (RMModInt128(*this) /= a); }
  template <class T> friend RMModInt128 operator+(T a, const RMModInt128 &b) { return (RMModInt128(a) += b); }
  template <class T> friend RMModInt128 operator-(T a, const RMModInt128 &b) { return (RMModInt128(a) -= b); }
  template <class T> friend RMModInt128 operator*(T a, const RMModInt128 &b) { return (RMModInt128(a) *= b); }
  template <class T> friend RMModInt128 operator/(T a, const RMModInt128 &b) { return (RMModInt128(a) /= b); }
  explicit operator bool() const { return y; }
  bool operator==(const RMModInt128 &a) const { return (y == a.y); }
  bool operator!=(const RMModInt128 &a) const { return (y != a.y); }
  friend std::ostream &operator<<(std::ostream &os, const RMModInt128 &a) { return os << get(); }
};
template <int ID> unsigned __int128 RMModInt128<ID>::M;
template <int ID> unsigned __int128 RMModInt128<ID>::INV_M;
template <int ID> unsigned __int128 RMModInt128<ID>::TWO256;
////////////////////////////////////////////////////////////////////////////////

#endif  // LIBRA_ALGEBRA_MODINT128_H_
