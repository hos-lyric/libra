#include <assert.h>
#include <string.h>
#include <initializer_list>
#include <ostream>

#include "fft998244353.h"
#include "modint.h"

using std::min;
using std::vector;

// For log.
constexpr int LIM_INV = 1 << 20;  // @
Mint inv[LIM_INV];
struct ModIntPreparator {
  ModIntPreparator() {
    inv[1] = 1;
    for (int i = 2; i < LIM_INV; ++i) inv[i] = -((Mint::M / i) * inv[Mint::M % i]);
  }
} preparator;

constexpr int LIM_POLY = 1 << 20;  // @
static_assert(LIM_POLY <= 1 << FFT_MAX);
Mint polyWork0[LIM_POLY], polyWork1[LIM_POLY];

struct Poly : public vector<Mint> {
  Poly() {}
  explicit Poly(int n) : vector<Mint>(n) {}
  Poly(const vector<Mint> &vec) : vector<Mint>(vec) {}
  Poly(std::initializer_list<Mint> il) : vector<Mint>(il) {}
  int size() const { return vector<Mint>::size(); }
  Poly take(int n) const { return Poly(vector<Mint>(data(), data() + min(n, size()))); }
  friend std::ostream &operator<<(std::ostream &os, const Poly &fs) {
    os << "[";
    for (int i = 0; i < fs.size(); ++i) { if (i > 0) os << ", "; os << fs[i]; }
    return os << "]";
  }

  Poly &operator+=(const Poly &fs) {
    if (size() < fs.size()) resize(fs.size());
    for (int i = 0; i < fs.size(); ++i) (*this)[i] += fs[i];
    return *this;
  }
  Poly &operator-=(const Poly &fs) {
    if (size() < fs.size()) resize(fs.size());
    for (int i = 0; i < fs.size(); ++i) (*this)[i] -= fs[i];
    return *this;
  }
  // 1 M(n)
  Poly &operator*=(const Poly &fs) {
    if (empty() || fs.empty()) return *this = {};
    const int nt = size(), nf = fs.size();
    int n = 1;
    for (; n < nt + nf - 1; n <<= 1) {}
    assert(n <= LIM_POLY);
    resize(n);
    fft(data(), n);
    memcpy(polyWork0, fs.data(), nf * sizeof(Mint));
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
    Poly fs(size());
    for (int i = 0; i < size(); ++i) fs[i] = -(*this)[i];
    return fs;
  }
  Poly operator+(const Poly &fs) const { return (Poly(*this) += fs); }
  Poly operator-(const Poly &fs) const { return (Poly(*this) -= fs); }
  Poly operator*(const Poly &fs) const { return (Poly(*this) *= fs); }
  Poly operator*(const Mint &a) const { return (Poly(*this) *= a); }
  Poly operator/(const Mint &a) const { return (Poly(*this) /= a); }
  friend Poly operator*(const Mint &a, const Poly &fs) { return fs * a; }

  // (5/3) M(n)
  // f <- f - (t f - 1) f
  Poly inv(int n) const {
    assert(!empty()); assert((*this)[0]); assert(1 <= n);
    assert(n <= 1 || 1 << (32 - __builtin_clz(n - 1)) <= LIM_POLY);
    Poly fs(n);
    fs[0] = (*this)[0].inv();
    for (int m = 1; m < n; m <<= 1) {
      memcpy(polyWork0, data(), min(m << 1, size()) * sizeof(Mint));
      memset(polyWork0 + min(m << 1, size()), 0, ((m << 1) - min(m << 1, size())) * sizeof(Mint));
      fft(polyWork0, m << 1);  // (1/3) M(n)
      memcpy(polyWork1, fs.data(), min(m << 1, n) * sizeof(Mint));
      memset(polyWork1 + min(m << 1, n), 0, ((m << 1) - min(m << 1, n)) * sizeof(Mint));
      fft(polyWork1, m << 1);  // (1/3) M(n)
      for (int i = 0; i < m << 1; ++i) polyWork0[i] *= polyWork1[i];
      invFft(polyWork0, m << 1); // (1/3) M(n)
      memset(polyWork0, 0, m * sizeof(Mint));
      fft(polyWork0, m << 1); // (1/3) M(n)
      for (int i = 0; i < m << 1; ++i) polyWork0[i] *= polyWork1[i];
      invFft(polyWork0, m << 1); // (1/3) M(n)
      for (int i = m, i0 = min(m << 1, n); i < i0; ++i) fs[i] = -polyWork0[i];
    }
    return fs;
  }
  // (3/2) M(n)
  // Use (4 m)-th roots of unity to lift from (mod x^m) to (mod x^(2m)).
  // f <- f - (t f - 1) f
  // mod (x^(2m) - 1) (x^m - 1^(1/4))
  /*
  Poly inv(int n) const {
    assert(!empty()); assert((*this)[0]); assert(1 <= n);
    assert(n <= 1 || 3 << (31 - __builtin_clz(n - 1)) <= LIM_POLY);
    assert(n <= 1 << (FFT_MAX - 1));
    Poly fs(n);
    fs[0] = (*this)[0].inv();
    for (int h = 2, m = 1; m < n; ++h, m <<= 1) {
      const Mint a = FFT_ROOTS[h], b = INV_FFT_ROOTS[h];
      memcpy(polyWork0, data(), min(m << 1, size()) * sizeof(Mint));
      memset(polyWork0 + min(m << 1, size()), 0, ((m << 1) - min(m << 1, size())) * sizeof(Mint));
      {
        Mint aa = 1;
        for (int i = 0; i < m; ++i) { polyWork0[(m << 1) + i] = aa * polyWork0[i]; aa *= a; }
        for (int i = 0; i < m; ++i) { polyWork0[(m << 1) + i] += aa * polyWork0[m + i]; aa *= a; }
      }
      fft(polyWork0, m << 1);  // (1/3) M(n)
      fft(polyWork0 + (m << 1), m);  // (1/6) M(n)
      memcpy(polyWork1, fs.data(), min(m << 1, n) * sizeof(Mint));
      memset(polyWork1 + min(m << 1, n), 0, ((m << 1) - min(m << 1, n)) * sizeof(Mint));
      {
        Mint aa = 1;
        for (int i = 0; i < m; ++i) { polyWork1[(m << 1) + i] = aa * polyWork1[i]; aa *= a; }
        for (int i = 0; i < m; ++i) { polyWork1[(m << 1) + i] += aa * polyWork1[m + i]; aa *= a; }
      }
      fft(polyWork1, m << 1);  // (1/3) M(n)
      fft(polyWork1 + (m << 1), m);  // (1/6) M(n)
      for (int i = 0; i < (m << 1) + m; ++i) polyWork0[i] *= polyWork1[i] * polyWork1[i];
      invFft(polyWork0, m << 1);  // (1/3) M(n)
      invFft(polyWork0 + (m << 1), m);  // (1/6) M(n)
      // 2 f0 + (-f2), (-f1) + (-f3), 1^(1/4) (-f1) - (-f2) - 1^(1/4) (-f3)
      {
        Mint bb = 1;
        for (int i = 0, i0 = min(m, n - m); i < i0; ++i) {
          unsigned x = polyWork0[i].x + (bb * polyWork0[(m << 1) + i]).x + MO2 - (fs[i].x << 1);  // < 4 MO
          fs[m + i] = Mint(static_cast<unsigned long long>(FFT_ROOTS[2].x) * x) - polyWork0[m + i];
          fs[m + i].x = ((fs[m + i].x & 1) ? (fs[m + i].x + MO) : fs[m + i].x) >> 1;
          bb *= b;
        }
      }
    }
    return fs;
  }
  */
  // (13/6) M(n)
  // h <- h - (f h - t) g
  Poly div(const Poly &fs, int n) const {
    assert(!empty()); assert(!fs.empty()); assert(fs[0]); assert(1 <= n);
    if (n == 1) return {(*this)[0] / fs[0]};
    const int m = 1 << (31 - __builtin_clz(n - 1));
    assert(m << 1 <= LIM_POLY);
    Poly gs = fs.inv(m);  // (5/6) M(n)
    gs.resize(m << 1);
    fft(gs.data(), m << 1);  // (1/6) M(n)
    memcpy(polyWork0, data(), min(m, size()) * sizeof(Mint));
    memset(polyWork0 + min(m, size()), 0, ((m << 1) - min(m, size())) * sizeof(Mint));
    fft(polyWork0, m << 1);  // (1/6) M(n)
    for (int i = 0; i < m << 1; ++i) polyWork0[i] *= gs[i];
    invFft(polyWork0, m << 1);  // (1/6) M(n)
    Poly hs(n);
    memcpy(hs.data(), polyWork0, m * sizeof(Mint));
    memset(polyWork0 + m, 0, m * sizeof(Mint));
    fft(polyWork0, m << 1);  // (1/6) M(n)
    memcpy(polyWork1, fs.data(), min(m << 1, fs.size()) * sizeof(Mint));
    memset(polyWork1 + min(m << 1, fs.size()), 0, ((m << 1) - min(m << 1, fs.size())) * sizeof(Mint));
    fft(polyWork1, m << 1);  // (1/6) M(n)
    for (int i = 0; i < m << 1; ++i) polyWork0[i] *= polyWork1[i];
    invFft(polyWork0, m << 1);  // (1/6) M(n)
    memset(polyWork0, 0, m * sizeof(Mint));
    for (int i = m, i0 = min(m << 1, size()); i < i0; ++i) polyWork0[i] -= (*this)[i];
    fft(polyWork0, m << 1);  // (1/6) M(n)
    for (int i = 0; i < m << 1; ++i) polyWork0[i] *= gs[i];
    invFft(polyWork0, m << 1);  // (1/6) M(n)
    for (int i = m; i < n; ++i) hs[i] = -polyWork0[i];
    return hs;
  }
  // (13/6) M(n)
  // D log(t) = (D t) / t
  Poly log(int n) const {
    assert(!empty()); assert((*this)[0].x == 1); assert(n <= LIM_INV);
    Poly fs = take(n);
    for (int i = 0; i < fs.size(); ++i) fs[i] *= i;
    fs = fs.div(*this, n);
    for (int i = 1; i < n; ++i) fs[i] *= ::inv[i];
    return fs;
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
  // div
  {
    const Poly as{2}, bs{3};
    const Poly cs{Mint(2) / 3, 0, 0};
    assert(as.div(bs, 1) == cs.take(1));
    assert(as.div(bs, 2) == cs.take(2));
    assert(as.div(bs, 3) == cs.take(3));
  }
  {
    const Poly as{3, 1, 4, 1, 5}, bs{9, 2, 6, 5, 3, 5};
    const Poly cs{Mint(1) / 3, Mint(1) / 27, Mint(52) / 243, Mint(-320) / 2187,
                  Mint(6175) / 19683, Mint(-51122) / 177147,
                  Mint(-248135) / 1594323, Mint(-250037) / 14348907,
                  Mint(31596649) / 129140163, Mint(-39963686) / 1162261467};
    assert(as.div(bs, 1) == cs.take(1));
    assert(as.div(bs, 2) == cs.take(2));
    assert(as.div(bs, 3) == cs.take(3));
    assert(as.div(bs, 5) == cs.take(5));
    assert(as.div(bs, 8) == cs.take(8));
    assert(as.div(bs, 10) == cs.take(10));
  }
  // log
  {
    const Poly as{1, 8, 2, -8, -1, -8, 2, -8, -4, 5};
    const Poly bs{0, 8, -30, Mint(440) / 3, -835, Mint(25328) / 5, -32068,
                  Mint(1461776) / 7, Mint(-2776609) / 2, Mint(84385997) / 9,
                  -64116076};
    assert(as.log(1) == bs.take(1));
    assert(as.log(2) == bs.take(2));
    assert(as.log(3) == bs.take(3));
    assert(as.log(5) == bs.take(5));
    assert(as.log(8) == bs.take(8));
    assert(as.log(10) == bs.take(10));
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
    for (int i = 1; i < N; ++i) {
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
  solve_inv(1, 236309389);
  solve_inv(10, 855277511);
  solve_inv(100, 594998919);
  solve_inv(1000, 826080596);
  solve_inv(10000, 1054298238);
  solve_inv(100000, 102902713);
  solve_inv(1000000, 520886679);
  // 5/3: 15876 msec @ DAIVRabbit
  // 3/2: 16125 msec @ DAIVRabbit
}

void solve_log(const int N, const unsigned expected) {
  static constexpr int NUM_CASES = 100;
  const auto timerBegin = std::chrono::high_resolution_clock::now();

  unsigned ans = 0;
  for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
    Poly as(N);
    as[0] = 1;
    for (int i = 1; i < N; ++i) {
      as[i] = xrand();
    }
    const Poly bs = as.log(N);
    assert(bs.size() == N);
    for (int i = 0; i < N; ++i) {
      ans ^= (bs[i].x + i);
    }
  }

  const auto timerEnd = std::chrono::high_resolution_clock::now();
  cerr << "[log] " << NUM_CASES << " cases, N = " << N
       << ": expected = " << expected << ", actual = " << ans << endl;
  cerr << std::chrono::duration_cast<std::chrono::milliseconds>(
      timerEnd - timerBegin).count() << " msec" << endl;
  assert(expected == ans);
}
void measurement_log() {
  solve_log(1, 0);
  solve_log(10, 782075849);
  solve_log(100, 657181233);
  solve_log(1000, 196435197);
  solve_log(10000, 748203336);
  solve_log(100000, 482239467);
  solve_log(1000000, 515787875);
  // 21674 msec @ DAIVRabbit
}

int main() {
  unittest();
  measurement_inv();
  measurement_log();
  return 0;
}
