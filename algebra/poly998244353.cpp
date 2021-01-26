#include <assert.h>
#include <string.h>
#include <initializer_list>
#include <iostream>

#include "fft998244353.h"
#include "modint.h"

using std::min;
using std::vector;

// inv: log, exp, pow
constexpr int LIM_INV = 1 << 20;  // @
Mint inv[LIM_INV];
struct ModIntPreparator {
  ModIntPreparator() {
    inv[1] = 1;
    for (int i = 2; i < LIM_INV; ++i) inv[i] = -((Mint::M / i) * inv[Mint::M % i]);
  }
} preparator;

// polyWork0: operator*, inv, div, divAt, log, exp, pow
// polyWork1: inv, div, divAt, log, exp, pow
// polyWork2: divAt, exp, pow
// polyWork3: exp, pow
static constexpr int LIM_POLY = 1 << 20;  // @
static_assert(LIM_POLY <= 1 << FFT_MAX);
static Mint polyWork0[LIM_POLY], polyWork1[LIM_POLY], polyWork2[LIM_POLY], polyWork3[LIM_POLY];

struct Poly : public vector<Mint> {
  Poly() {}
  explicit Poly(int n) : vector<Mint>(n) {}
  Poly(const vector<Mint> &vec) : vector<Mint>(vec) {}
  Poly(std::initializer_list<Mint> il) : vector<Mint>(il) {}
  int size() const { return vector<Mint>::size(); }
  Mint at(long long k) const { return (0 <= k && k < size()) ? (*this)[k] : 0U; }
  int ord() const { for (int i = 0; i < size(); ++i) if ((*this)[i]) return i; return -1; }
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
  // 3 E(|t| + |f|)
  Poly &operator*=(const Poly &fs) {
    if (empty() || fs.empty()) return *this = {};
    const int nt = size(), nf = fs.size();
    int n = 1;
    for (; n < nt + nf - 1; n <<= 1) {}
    assert(n <= LIM_POLY);
    resize(n);
    fft(data(), n);  // 1 E(n)
    memcpy(polyWork0, fs.data(), nf * sizeof(Mint));
    memset(polyWork0 + nf, 0, (n - nf) * sizeof(Mint));
    fft(polyWork0, n);  // 1 E(n)
    for (int i = 0; i < n; ++i) (*this)[i] *= polyWork0[i];
    invFft(data(), n);  // 1 E(n)
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

  // 10 E(n)
  // f <- f - (t f - 1) f
  Poly inv(int n) const {
    assert(!empty()); assert((*this)[0]); assert(1 <= n);
    assert(n == 1 || 1 << (32 - __builtin_clz(n - 1)) <= LIM_POLY);
    Poly fs(n);
    fs[0] = (*this)[0].inv();
    for (int m = 1; m < n; m <<= 1) {
      memcpy(polyWork0, data(), min(m << 1, size()) * sizeof(Mint));
      memset(polyWork0 + min(m << 1, size()), 0, ((m << 1) - min(m << 1, size())) * sizeof(Mint));
      fft(polyWork0, m << 1);  // 2 E(n)
      memcpy(polyWork1, fs.data(), min(m << 1, n) * sizeof(Mint));
      memset(polyWork1 + min(m << 1, n), 0, ((m << 1) - min(m << 1, n)) * sizeof(Mint));
      fft(polyWork1, m << 1);  // 2 E(n)
      for (int i = 0; i < m << 1; ++i) polyWork0[i] *= polyWork1[i];
      invFft(polyWork0, m << 1); // 2 E(n)
      memset(polyWork0, 0, m * sizeof(Mint));
      fft(polyWork0, m << 1); // 2 E(n)
      for (int i = 0; i < m << 1; ++i) polyWork0[i] *= polyWork1[i];
      invFft(polyWork0, m << 1); // 2 E(n)
      for (int i = m, i0 = min(m << 1, n); i < i0; ++i) fs[i] = -polyWork0[i];
    }
    return fs;
  }
  // 9 E(n)
  // Need (4 m)-th roots of unity to lift from (mod x^m) to (mod x^(2m)).
  // f <- f - (t f - 1) f
  // (t f^2) mod ((x^(2m) - 1) (x^m - 1^(1/4)))
  /*
  Poly inv(int n) const {
    assert(!empty()); assert((*this)[0]); assert(1 <= n);
    assert(n == 1 || 3 << (31 - __builtin_clz(n - 1)) <= LIM_POLY);
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
      fft(polyWork0, m << 1);  // 2 E(n)
      fft(polyWork0 + (m << 1), m);  // 1 E(n)
      memcpy(polyWork1, fs.data(), min(m << 1, n) * sizeof(Mint));
      memset(polyWork1 + min(m << 1, n), 0, ((m << 1) - min(m << 1, n)) * sizeof(Mint));
      {
        Mint aa = 1;
        for (int i = 0; i < m; ++i) { polyWork1[(m << 1) + i] = aa * polyWork1[i]; aa *= a; }
        for (int i = 0; i < m; ++i) { polyWork1[(m << 1) + i] += aa * polyWork1[m + i]; aa *= a; }
      }
      fft(polyWork1, m << 1);  // 2 E(n)
      fft(polyWork1 + (m << 1), m);  // 1 E(n)
      for (int i = 0; i < (m << 1) + m; ++i) polyWork0[i] *= polyWork1[i] * polyWork1[i];
      invFft(polyWork0, m << 1);  // 2 E(n)
      invFft(polyWork0 + (m << 1), m);  // 1 E(n)
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
  // 13 E(n)
  // g = (1 / f) mod x^m
  // h <- h - (f h - t) g
  Poly div(const Poly &fs, int n) const {
    assert(!empty()); assert(!fs.empty()); assert(fs[0]); assert(1 <= n);
    if (n == 1) return {(*this)[0] / fs[0]};
    // m < n <= 2 m
    const int m = 1 << (31 - __builtin_clz(n - 1));
    assert(m << 1 <= LIM_POLY);
    Poly gs = fs.inv(m);  // 5 E(n)
    gs.resize(m << 1);
    fft(gs.data(), m << 1);  // 1 E(n)
    memcpy(polyWork0, data(), min(m, size()) * sizeof(Mint));
    memset(polyWork0 + min(m, size()), 0, ((m << 1) - min(m, size())) * sizeof(Mint));
    fft(polyWork0, m << 1);  // 1 E(n)
    for (int i = 0; i < m << 1; ++i) polyWork0[i] *= gs[i];
    invFft(polyWork0, m << 1);  // 1 E(n)
    Poly hs(n);
    memcpy(hs.data(), polyWork0, m * sizeof(Mint));
    memset(polyWork0 + m, 0, m * sizeof(Mint));
    fft(polyWork0, m << 1);  // 1 E(n)
    memcpy(polyWork1, fs.data(), min(m << 1, fs.size()) * sizeof(Mint));
    memset(polyWork1 + min(m << 1, fs.size()), 0, ((m << 1) - min(m << 1, fs.size())) * sizeof(Mint));
    fft(polyWork1, m << 1);  // 1 E(n)
    for (int i = 0; i < m << 1; ++i) polyWork0[i] *= polyWork1[i];
    invFft(polyWork0, m << 1);  // 1 E(n)
    memset(polyWork0, 0, m * sizeof(Mint));
    for (int i = m, i0 = min(m << 1, size()); i < i0; ++i) polyWork0[i] -= (*this)[i];
    fft(polyWork0, m << 1);  // 1 E(n)
    for (int i = 0; i < m << 1; ++i) polyWork0[i] *= gs[i];
    invFft(polyWork0, m << 1);  // 1 E(n)
    for (int i = m; i < n; ++i) hs[i] = -polyWork0[i];
    return hs;
  }
  // (4 (floor(log_2 k) - ceil(log_2 |fs|)) + 16) E(|fs|)
  // [x^k] (t(x) / f(x)) = [x^k] ((t(x) f(-x)) / (f(x) f(-x))
  // polyWork0: half of (2 m)-th roots of unity, inversed, bit-reversed
  Mint divAt(const Poly &fs, long long k) const {
    assert(k >= 0);
    if (size() >= fs.size()) {
      // TODO: operator%
      assert(false);
    }
    int h = 0, m = 1;
    for (; m < fs.size(); ++h, m <<= 1) {}
    if (k < m) {
      const Poly gs = fs.inv(k + 1);  // 10 E(|fs|)
      Mint sum;
      for (int i = 0, i0 = min<int>(k + 1, size()); i < i0; ++i) sum += (*this)[i] * gs[k - i];
      return sum;
    }
    assert(m << 1 <= LIM_POLY);
    polyWork0[0] = Mint(2U).inv();
    for (int hh = 0; hh < h; ++hh) for (int i = 0; i < 1 << hh; ++i) polyWork0[1 << hh | i] = polyWork0[i] * INV_FFT_ROOTS[hh + 2];
    const Mint a = FFT_ROOTS[h + 1];
    memcpy(polyWork2, data(), size() * sizeof(Mint));
    memset(polyWork2 + size(), 0, ((m << 1) - size()) * sizeof(Mint));
    fft(polyWork2, m << 1);  // 2 E(|fs|)
    memcpy(polyWork1, fs.data(), fs.size() * sizeof(Mint));
    memset(polyWork1 + fs.size(), 0, ((m << 1) - fs.size()) * sizeof(Mint));
    fft(polyWork1, m << 1);  // 2 E(|fs|)
    for (; ; ) {
      if (k & 1) {
        for (int i = 0; i < m; ++i) polyWork2[i] = polyWork0[i] * (polyWork2[i << 1 | 0] * polyWork1[i << 1 | 1] - polyWork2[i << 1 | 1] * polyWork1[i << 1 | 0]);
      } else {
        for (int i = 0; i < m; ++i) {
          polyWork2[i] = polyWork2[i << 1 | 0] * polyWork1[i << 1 | 1] + polyWork2[i << 1 | 1] * polyWork1[i << 1 | 0];
          polyWork2[i].x = ((polyWork2[i].x & 1) ? (polyWork2[i].x + MO) : polyWork2[i].x) >> 1;
        }
      }
      for (int i = 0; i < m; ++i) polyWork1[i] = polyWork1[i << 1 | 0] * polyWork1[i << 1 | 1];
      if ((k >>= 1) < m) {
        invFft(polyWork2, m);  // 1 E(|fs|)
        invFft(polyWork1, m);  // 1 E(|fs|)
        // Poly::inv does not use polyWork2
        const Poly gs = Poly(vector<Mint>(polyWork1, polyWork1 + k + 1)).inv(k + 1);  // 10 E(|fs|)
        Mint sum;
        for (int i = 0; i <= k; ++i) sum += polyWork2[i] * gs[k - i];
        return sum;
      }
      memcpy(polyWork2 + m, polyWork2, m * sizeof(Mint));
      invFft(polyWork2 + m, m);  // (floor(log_2 k) - ceil(log_2 |fs|)) E(|fs|)
      memcpy(polyWork1 + m, polyWork1, m * sizeof(Mint));
      invFft(polyWork1 + m, m);  // (floor(log_2 k) - ceil(log_2 |fs|)) E(|fs|)
      Mint aa = 1;
      for (int i = m; i < m << 1; ++i) { polyWork2[i] *= aa; polyWork1[i] *= aa; aa *= a; }
      fft(polyWork2 + m, m);  // (floor(log_2 k) - ceil(log_2 |fs|)) E(|fs|)
      fft(polyWork1 + m, m);  // (floor(log_2 k) - ceil(log_2 |fs|)) E(|fs|)
    }
  }
  // 13 E(n)
  // D log(t) = (D t) / t
  Poly log(int n) const {
    assert(!empty()); assert((*this)[0].x == 1U); assert(n <= LIM_INV);
    Poly fs = take(n);
    for (int i = 0; i < fs.size(); ++i) fs[i] *= i;
    fs = fs.div(*this, n);
    for (int i = 1; i < n; ++i) fs[i] *= ::inv[i];
    return fs;
  }
  // (16 + 1/2) E(n)
  // f = exp(t) mod x^m  ==>  (D f) / f == D t  (mod x^m)
  // g = (1 / exp(t)) mod x^m
  // f <- f - (log f - t) / (1 / f)
  //   =  f - (I ((D f) / f) - t) f
  //   == f - (I ((D f) / f + (f g - 1) ((D f) / f - D (t mod x^m))) - t) f  (mod x^(2m))
  //   =  f - (I (g (D f - f D (t mod x^m)) + D (t mod x^m)) - t) f
  // g <- g - (f g - 1) g
  // polyWork1: DFT(f, 2 m), polyWork2: g, polyWork3: DFT(g, 2 m)
  Poly exp(int n) const {
    assert(!empty()); assert(!(*this)[0]); assert(1 <= n);
    assert(n == 1 || 1 << (32 - __builtin_clz(n - 1)) <= min(LIM_INV, LIM_POLY));
    if (n == 1) return {1U};
    if (n == 2) return {1U, (1 < size()) ? (*this)[1] : 0U};
    Poly fs(n);
    fs[0].x = polyWork1[0].x = polyWork1[1].x = polyWork2[0].x = 1U;
    int m;
    for (m = 1; m << 1 < n; m <<= 1) {
      for (int i = 0, i0 = min(m, size()); i < i0; ++i) polyWork0[i] = i * (*this)[i];
      memset(polyWork0 + min(m, size()), 0, (m - min(m, size())) * sizeof(Mint));
      fft(polyWork0, m);  // (1/2) E(n)
      for (int i = 0; i < m; ++i) polyWork0[i] *= polyWork1[i];
      invFft(polyWork0, m);  // (1/2) E(n)
      for (int i = 0; i < m; ++i) polyWork0[i] -= i * fs[i];
      memset(polyWork0 + m, 0, m * sizeof(Mint));
      fft(polyWork0, m << 1);  // 1 E(n)
      memcpy(polyWork3, polyWork2, m * sizeof(Mint));
      memset(polyWork3 + m, 0, m * sizeof(Mint));
      fft(polyWork3, m << 1);  // 1 E(n)
      for (int i = 0; i < m << 1; ++i) polyWork0[i] *= polyWork3[i];
      invFft(polyWork0, m << 1);  // 1 E(n)
      for (int i = 0; i < m; ++i) polyWork0[i] *= ::inv[m + i];
      for (int i = 0, i0 = min(m, size() - m); i < i0; ++i) polyWork0[i] += (*this)[m + i];
      memset(polyWork0 + m, 0, m * sizeof(Mint));
      fft(polyWork0, m << 1);  // 1 E(n)
      for (int i = 0; i < m << 1; ++i) polyWork0[i] *= polyWork1[i];
      invFft(polyWork0, m << 1);  // 1 E(n)
      memcpy(fs.data() + m, polyWork0, m * sizeof(Mint));
      memcpy(polyWork1, fs.data(), (m << 1) * sizeof(Mint));
      memset(polyWork1 + (m << 1), 0, (m << 1) * sizeof(Mint));
      fft(polyWork1, m << 2);  // 2 E(n)
      for (int i = 0; i < m << 1; ++i) polyWork0[i] = polyWork1[i] * polyWork3[i];
      invFft(polyWork0, m << 1);  // 1 E(n)
      memset(polyWork0, 0, m * sizeof(Mint));
      fft(polyWork0, m << 1);  // 1 E(n)
      for (int i = 0; i < m << 1; ++i) polyWork0[i] *= polyWork3[i];
      invFft(polyWork0, m << 1);  // 1 E(n)
      for (int i = m; i < m << 1; ++i) polyWork2[i] = -polyWork0[i];
    }
    for (int i = 0, i0 = min(m, size()); i < i0; ++i) polyWork0[i] = i * (*this)[i];
    memset(polyWork0 + min(m, size()), 0, (m - min(m, size())) * sizeof(Mint));
    fft(polyWork0, m);  // (1/2) E(n)
    for (int i = 0; i < m; ++i) polyWork0[i] *= polyWork1[i];
    invFft(polyWork0, m);  // (1/2) E(n)
    for (int i = 0; i < m; ++i) polyWork0[i] -= i * fs[i];
    memcpy(polyWork0 + m, polyWork0 + (m >> 1), (m >> 1) * sizeof(Mint));
    memset(polyWork0 + (m >> 1), 0, (m >> 1) * sizeof(Mint));
    memset(polyWork0 + m + (m >> 1), 0, (m >> 1) * sizeof(Mint));
    fft(polyWork0, m);  // (1/2) E(n)
    fft(polyWork0 + m, m);  // (1/2) E(n)
    memcpy(polyWork3 + m, polyWork2 + (m >> 1), (m >> 1) * sizeof(Mint));
    memset(polyWork3 + m + (m >> 1), 0, (m >> 1) * sizeof(Mint));
    fft(polyWork3 + m, m);  // (1/2) E(n)
    for (int i = 0; i < m; ++i) polyWork0[m + i] = polyWork0[i] * polyWork3[m + i] + polyWork0[m + i] * polyWork3[i];
    for (int i = 0; i < m; ++i) polyWork0[i] *= polyWork3[i];
    invFft(polyWork0, m);  // (1/2) E(n)
    invFft(polyWork0 + m, m);  // (1/2) E(n)
    for (int i = 0; i < m >> 1; ++i) polyWork0[(m >> 1) + i] += polyWork0[m + i];
    for (int i = 0; i < m; ++i) polyWork0[i] *= ::inv[m + i];
    for (int i = 0, i0 = min(m, size() - m); i < i0; ++i) polyWork0[i] += (*this)[m + i];
    memset(polyWork0 + m, 0, m * sizeof(Mint));
    fft(polyWork0, m << 1);  // 1 E(n)
    for (int i = 0; i < m << 1; ++i) polyWork0[i] *= polyWork1[i];
    invFft(polyWork0, m << 1);  // 1 E(n)
    memcpy(fs.data() + m, polyWork0, (n - m) * sizeof(Mint));
    return fs;
  }
  // (29 + 1/2) E(n)
  // g <- g - (log g - a log t) g
  Poly pow(long long a, int n) const {
    assert(1 <= n);
    if (empty() || (*this)[0].x != 1U) {
      assert(a >= 0);
      if (a == 0) { Poly gs(n); gs[0].x = 1U; return gs; }
      const int o = ord();
      if (o == -1 || o > (n - 1) / a) return Poly(n);
      const Mint b = (*this)[o].inv(), c = (*this)[o].pow(a);
      const int ntt = min<int>(n - a * o, size() - o);
      Poly tts(ntt);
      for (int i = 0; i < ntt; ++i) tts[i] = b * (*this)[o + i];
      tts = tts.pow(a, n - a * o);
      Poly gs(n);
      for (int i = 0; i < n - a * o; ++i) gs[a * o + i] = c * tts[i];
      return gs;
    }
    assert(!empty()); assert((*this)[0].x == 1);
    return (a * log(n)).exp(n);  // 13 E(n) + (16 + 1/2) E(n)
  }
};

Mint linearRecurrenceAt(const vector<Mint> &as, const vector<Mint> &cs, long long k) {
  assert(!cs.empty()); assert(cs[0]);
  const int d = cs.size() - 1;
  assert(as.size() >= static_cast<size_t>(d));
  return (Poly(vector<Mint>(as.begin(), as.begin() + d)) * cs).take(d).divAt(cs, k);
}

// -----------------------------------------------------------------------------

#include <chrono>
#include <iostream>
using std::cerr;
using std::endl;

void unittest() {
  // at
  {
    assert((Poly{3, 1, 4, 1}).at(-1) == 0);
    assert((Poly{3, 1, 4, 1}).at(2) == 4);
    assert((Poly{3, 1, 4, 1}).at(4) == 0);
    assert((Poly{3, 1, 4, 1}).at(1LL << 32) == 0);
  }
  // ord
  {
    assert((Poly{}).ord() == -1);
    assert((Poly{1}).ord() == 0);
    assert((Poly{0}).ord() == -1);
    assert((Poly{3, 1, 4, 1}).ord() == 0);
    assert((Poly{0, 1, 0, 1}).ord() == 1);
    assert((Poly{0, 0, 0, 1}).ord() == 3);
    assert((Poly{0, 0, 0, 0}).ord() == -1);
  }
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
  // divAt
  {
    const Poly as{};
    const Poly bs{2};
    assert(as.divAt(bs, 0) == 0);
    assert(as.divAt(bs, 1) == 0);
    assert(as.divAt(bs, 2) == 0);
    assert(as.divAt(bs, 3) == 0);
    assert(as.divAt(bs, 4) == 0);
  }
  {
    const Poly as{2};
    const Poly bs{3, 4};
    assert(as.divAt(bs, 0) == Mint(2) / 3);
    assert(as.divAt(bs, 1) == Mint(-8) / 9);
    assert(as.divAt(bs, 2) == Mint(32) / 27);
    assert(as.divAt(bs, 3) == Mint(-128) / 81);
    assert(as.divAt(bs, 4) == Mint(512) / 243);
  }
  {
    const Poly as{0, 1};
    const Poly bs{1, -1, -1};
    assert(as.divAt(bs, 0) == 0);
    assert(as.divAt(bs, 1) == 1);
    assert(as.divAt(bs, 2) == 1);
    assert(as.divAt(bs, 3) == 2);
    assert(as.divAt(bs, 4) == 3);
    assert(as.divAt(bs, 5) == 5);
    assert(as.divAt(bs, 6) == 8);
    assert(as.divAt(bs, 7) == 13);
    assert(as.divAt(bs, 8) == 21);
    assert(as.divAt(bs, 9) == 34);
    assert(as.divAt(bs, 10) == 55);
    assert(as.divAt(bs, 1000000000000000000LL) == Mint(23849548U));
  }
  {
    const Poly as{3, 1, 4, 1, 5, 9};
    const Poly bs{2, 7, 1, 8, 2, 8, 1, 8};
    assert(as.divAt(bs, 0) == Mint(3) / 2);
    assert(as.divAt(bs, 1) == Mint(-19) / 4);
    assert(as.divAt(bs, 2) == Mint(143) / 8);
    assert(as.divAt(bs, 9) == Mint(-162213091) / 1024);
    assert(as.divAt(bs, 10) == Mint(1188773543) / 2048);
    assert(as.divAt(bs, 11) == Mint(-8711858971LL) / 4096);
    assert(as.divAt(bs, 19) == Mint(-72477705834111867LL) / 1048576);
    assert(as.divAt(bs, 20) == Mint(531148740030089567LL) / 2097152);
    assert(as.divAt(bs, 21) == Mint(-3892493295581025139LL) / 4194304);
  }
  // log
  {
    const Poly as{1};
    const Poly bs{0, 0};
    assert(as.log(1) == bs.take(1));
    assert(as.log(2) == bs.take(2));
  }
  {
    const Poly as{1, 2};
    const Poly bs{0, 2, -2};
    assert(as.log(1) == bs.take(1));
    assert(as.log(2) == bs.take(2));
    assert(as.log(3) == bs.take(3));
  }
  {
    const Poly as{1, 3, 4};
    const Poly bs{0, 3, Mint(-1) / 2, -3};
    assert(as.log(1) == bs.take(1));
    assert(as.log(2) == bs.take(2));
    assert(as.log(3) == bs.take(3));
    assert(as.log(4) == bs.take(4));
  }
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
  // exp
  {
    const Poly as{0};
    const Poly bs{1, 0};
    assert(as.exp(1) == bs.take(1));
    assert(as.exp(2) == bs.take(2));
  }
  {
    const Poly as{0, 2};
    const Poly bs{1, 2, 2};
    assert(as.exp(1) == bs.take(1));
    assert(as.exp(2) == bs.take(2));
    assert(as.exp(3) == bs.take(3));
  }
  {
    const Poly as{0, 3, 4};
    const Poly bs{1, 3, Mint(17) / 2, Mint(33) / 2};
    assert(as.exp(1) == bs.take(1));
    assert(as.exp(2) == bs.take(2));
    assert(as.exp(3) == bs.take(3));
    assert(as.exp(4) == bs.take(4));
  }
  {
    const Poly as{0, 8, 2, -8, -1, -8, 2, -8, -4, 5};
    const Poly bs{1, 8, 34, Mint(280) / 3, Mint(515) / 3, Mint(2576) / 15,
                  Mint(-4676) / 45, Mint(-268096) / 315, Mint(-249449) / 126,
                  Mint(-1593721) / 567};
    assert(as.exp(1) == bs.take(1));
    assert(as.exp(2) == bs.take(2));
    assert(as.exp(3) == bs.take(3));
    assert(as.exp(5) == bs.take(5));
    assert(as.exp(8) == bs.take(8));
    assert(as.exp(10) == bs.take(10));
  }
  // pow
  {
    const Poly as{};
    const Poly bs{1, 0};
    assert(as.pow(0, 1) == bs.take(1));
    assert(as.pow(0, 2) == bs.take(2));
  }
  {
    const Poly as{};
    const Poly bs{0, 0};
    assert(as.pow(10, 1) == bs.take(1));
    assert(as.pow(10, 2) == bs.take(2));
  }
  {
    const Poly as{2};
    const Poly bs{1024, 0};
    assert(as.pow(10, 1) == bs.take(1));
    assert(as.pow(10, 2) == bs.take(2));
  }
  {
    const Poly as{1, 3, 4};
    const Poly bs{1, 15, 110, 510};
    assert(as.pow(5, 1) == bs.take(1));
    assert(as.pow(5, 2) == bs.take(2));
    assert(as.pow(5, 3) == bs.take(3));
    assert(as.pow(5, 4) == bs.take(4));
  }
  {
    const Poly as{0, 0, 3, 1, 4, 1, 5, 9, 2, 6};
    const Poly bs{0, 0, 0, 0, 0, 0, 27, 27, 117, 100, 309, 456};
    assert(as.pow(3, 1) == bs.take(1));
    assert(as.pow(3, 2) == bs.take(2));
    assert(as.pow(3, 3) == bs.take(3));
    assert(as.pow(3, 5) == bs.take(5));
    assert(as.pow(3, 8) == bs.take(8));
    assert(as.pow(3, 10) == bs.take(10));
    assert(as.pow(3, 12) == bs.take(12));
  }
  // linearRecurrenceAt
  {
    const vector<Mint> as{0, 1, 1, 2};
    const vector<Mint> cs{1, -1, -1};
    assert(linearRecurrenceAt(as, cs, 0) == 0);
    assert(linearRecurrenceAt(as, cs, 1) == 1);
    assert(linearRecurrenceAt(as, cs, 2) == 1);
    assert(linearRecurrenceAt(as, cs, 3) == 2);
    assert(linearRecurrenceAt(as, cs, 7) == 13);
    assert(linearRecurrenceAt(as, cs, 8) == 21);
    assert(linearRecurrenceAt(as, cs, 1000000000000000000) == Mint(23849548U));
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

void solve_exp(const int N, const unsigned expected) {
  static constexpr int NUM_CASES = 100;
  const auto timerBegin = std::chrono::high_resolution_clock::now();

  unsigned ans = 0;
  for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
    Poly as(N);
    as[0] = 0;
    for (int i = 1; i < N; ++i) {
      as[i] = xrand();
    }
    const Poly bs = as.exp(N);
    assert(bs.size() == N);
    for (int i = 0; i < N; ++i) {
      ans ^= (bs[i].x + i);
    }
  }

  const auto timerEnd = std::chrono::high_resolution_clock::now();
  cerr << "[exp] " << NUM_CASES << " cases, N = " << N
       << ": expected = " << expected << ", actual = " << ans << endl;
  cerr << std::chrono::duration_cast<std::chrono::milliseconds>(
      timerEnd - timerBegin).count() << " msec" << endl;
  assert(expected == ans);
}
void measurement_exp() {
  solve_exp(1, 0);
  solve_exp(10, 552854624);
  solve_exp(100, 1012444333);
  solve_exp(1000, 201206437);
  solve_exp(10000, 24842905);
  solve_exp(100000, 674622497);
  solve_exp(1000000, 197978996);
  // 25017 msec @ DAIVRabbit
}

int main() {
  unittest();
  measurement_inv();
  measurement_log();
  measurement_exp();
  return 0;
}
