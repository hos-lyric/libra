#include <assert.h>
#include <string.h>
#include <initializer_list>
#include <ostream>

#include "fft998244353.h"

using std::min;
using std::vector;

constexpr int LIM_POLY = 1 << 20;
Mint polyWork0[LIM_POLY], polyWork1[LIM_POLY];

struct Poly : public vector<Mint> {
  Poly() {}
  explicit Poly(int n) : vector<Mint>(n) {}
  Poly(const vector<Mint> &vec) : vector<Mint>(vec) {}
  Poly(std::initializer_list<Mint> il) : vector<Mint>(il) {}
  int size() const { return vector<Mint>::size(); }
  Poly take(int n) const { return Poly(vector<Mint>(data(), data() + min(n, size()))); }
  friend std::ostream &operator<<(std::ostream &os, const Poly &f) {
    os << "[";
    for (int i = 0; i < f.size(); ++i) { if (i > 0) os << ", "; os << f[i]; }
    return os << "]";
  }

  Poly &operator+=(const Poly &f) {
    if (size() < f.size()) resize(f.size());
    for (int i = 0; i < f.size(); ++i) (*this)[i] += f[i];
    return *this;
  }
  Poly &operator-=(const Poly &f) {
    if (size() < f.size()) resize(f.size());
    for (int i = 0; i < f.size(); ++i) (*this)[i] -= f[i];
    return *this;
  }
  // 1 M(n)
  Poly &operator*=(const Poly &f) {
    if (empty() || f.empty()) return *this = {};
    const int nt = size(), nf = f.size();
    int n = 1;
    for (; n < nt + nf - 1; n <<= 1) {}
    resize(n);
    fft(data(), n);
    memcpy(polyWork0, f.data(), nf * sizeof(Mint));
    memset(polyWork0 + nf, 0, (n - nf) * sizeof(Mint));
    fft(polyWork0, n);
    for (int i = 0; i < n; ++i) (*this)[i] *= polyWork0[i];
    invFft(data(), n);
    resize(nt + nf - 1);
    return *this;
  }
  Poly &operator*=(const Mint &a) {
    for (int i = 0; i < size(); ++i) (*this)[i] *= a;
    return *this;
  }
  Poly &operator/=(const Mint &a) {
    const Mint b = a.inv();
    for (int i = 0; i < size(); ++i) (*this)[i] *= b;
    return *this;
  }
  Poly operator+() const { return *this; }
  Poly operator-() const {
    Poly f(size());
    for (int i = 0; i < size(); ++i) f[i] = -(*this)[i];
    return f;
  }
  Poly operator+(const Poly &f) const { return (Poly(*this) += f); }
  Poly operator-(const Poly &f) const { return (Poly(*this) -= f); }
  Poly operator*(const Poly &f) const { return (Poly(*this) *= f); }
  Poly operator*(const Mint &a) const { return (Poly(*this) *= a); }
  Poly operator/(const Mint &a) const { return (Poly(*this) /= a); }
  friend Poly operator*(const Mint &a, const Poly &f) { return f * a; }

  // (5/3) M(n)
  // f <- f - (t f - 1) f
  Poly inv(int n) const {
    assert(!empty()); assert((*this)[0]); assert(n >= 1);
    Poly f(n);
    f[0] = (*this)[0].inv();
    for (int m = 1; m < n; m <<= 1) {
      memcpy(polyWork0, data(), min(m << 1, size()) * sizeof(Mint));
      memset(polyWork0 + min(m << 1, size()), 0, ((m << 1) - min(m << 1, size())) * sizeof(Mint));
      fft(polyWork0, m << 1);
      memcpy(polyWork1, f.data(), min(m << 1, n) * sizeof(Mint));
      memset(polyWork1 + min(m << 1, n), 0, ((m << 1) - min(m << 1, n)) * sizeof(Mint));
      fft(polyWork1, m << 1);
      for (int i = 0; i < m << 1; ++i) polyWork0[i] *= polyWork1[i];
      invFft(polyWork0, m << 1);
      memset(polyWork0, 0, m * sizeof(Mint));
      fft(polyWork0, m << 1);
      for (int i = 0; i < m << 1; ++i) polyWork0[i] *= polyWork1[i];
      invFft(polyWork0, m << 1);
      for (int i = m, i0 = min(m << 1, n); i < i0; ++i) f[i] = -polyWork0[i];
    }
    return f;
  }
};

// -----------------------------------------------------------------------------

#include <chrono>
#include <iostream>
using std::cerr;
using std::endl;

void unittest() {
  // take
  {
    const Poly as{3, 1, 4, 1};
    assert(as.take(0) == (vector<Mint>{}));
    assert(as.take(2) == (vector<Mint>{3, 1}));
    assert(as.take(4) == (vector<Mint>{3, 1, 4, 1}));
    assert(as.take(6) == (vector<Mint>{3, 1, 4, 1}));
  }

  // operator+()
  // operator-()
  {
    const Poly as{3, 1, -4, -1};
    assert(+as == (vector<Mint>{3, 1, -4, -1}));
    assert(-as == (vector<Mint>{-3, -1, 4, 1}));
  }
  // operator+(const Poly &)
  // operator-(const Poly &)
  {
    const Poly as{3, 1}, bs{4, 1, 5};
    assert(as + bs == (vector<Mint>{7, 2, 5}));
    assert(bs + as == (vector<Mint>{7, 2, 5}));
    assert(as - bs == (vector<Mint>{-1, 0, -5}));
    assert(bs - as == (vector<Mint>{1, 0, 5}));
  }
  // operator*(const Poly &)
  {
    const Poly as{3, 1, -4, -1}, bs{-5, 9, -2, 6, -5};
    assert(as * bs == (vector<Mint>{-15, 22, 23, -15, -10, -27, 14, 5}));
  }
  // operator*(const Mint &)
  // operator/(const Mint &)
  // friend operator*(const Poly &, const Mint &)
  {
    const Poly as{3, 1, -4, -1};
    assert(as * 2 == (vector<Mint>{6, 2, -8, -2}));
    assert(as / 2 ==
           (vector<Mint>{(MO + 3) / 2, (MO + 1) / 2, -2, (MO - 1) / 2}));
    assert(2 * as == (vector<Mint>{6, 2, -8, -2}));
  }

  // inv
  {
    const Poly as{3, 1, 4, 1, 5};
    const Poly bs{Mint(1) / 3, Mint(-1) / 9, Mint(-11) / 27, Mint(14) / 81,
                  Mint(-8) / 243, Mint(74) / 729, Mint(1381) / 2187,
                  Mint(-4087) / 6561, Mint(-12071) / 19683,
                  Mint(38696) / 59049};
    assert(as.inv(1) == bs.take(1));
    assert(as.inv(2) == bs.take(2));
    assert(as.inv(3) == bs.take(3));
    assert(as.inv(5) == bs.take(5));
    assert(as.inv(8) == bs.take(8));
    assert(as.inv(10) == bs.take(10));
  }
}

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void solve_inv(const int N, const unsigned expected) {
  static constexpr int NUM_CASES = 100;
  const auto timerBegin = std::chrono::high_resolution_clock::now();

  unsigned ans = 0;
  for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
    Poly as(N);
    as[0] = 1 + xrand() % (MO - 1);
    for (int i = 0; i < N; ++i) {
      as[i] = xrand();
    }
    const Poly bs = as.inv(N);
    assert(bs.size() == N);
    for (int i = 0; i < N; ++i) {
      ans ^= (bs[i].x + i);
    }
  }

  const auto timerEnd = std::chrono::high_resolution_clock::now();
  cerr << "[inv] " << NUM_CASES << " cases, N = " << N
       << ": expected = " << expected << ", actual = " << ans << endl;
  cerr << std::chrono::duration_cast<std::chrono::milliseconds>(
      timerEnd - timerBegin).count() << " msec" << endl;
  assert(expected == ans);
}
void measurement_inv() {
  solve_inv(1, 34918970);
  solve_inv(10, 754220679);
  solve_inv(100, 588377382);
  solve_inv(1000, 1032597331);
  solve_inv(10000, 109459152);
  solve_inv(100000, 934740919);
  solve_inv(1000000, 266783204);
  // 15876 msec @ DAIVRabbit
}

int main() {
  unittest();
  measurement_inv();
  return 0;
}
