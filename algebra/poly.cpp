#include <assert.h>
#include <stdio.h>
#include <algorithm>
#include <iostream>
#include <vector>

using std::max;
using std::min;
using std::vector;

template <int M_> struct ModInt {
  static constexpr int M = M_;
  int x;
  constexpr ModInt() : x(0) {}
  constexpr ModInt(long long x_) : x(x_ % M) { if (x < 0) x += M; }
  ModInt &operator+=(const ModInt &a) { x += a.x; if (x >= M) x -= M; return *this; }
  ModInt &operator-=(const ModInt &a) { x -= a.x; if (x < 0) x += M; return *this; }
  ModInt &operator*=(const ModInt &a) { x = static_cast<int>((static_cast<long long>(x) * a.x) % M); return *this; }
  ModInt operator+(const ModInt &a) const { return (ModInt(*this) += a); }
  ModInt operator-(const ModInt &a) const { return (ModInt(*this) -= a); }
  ModInt operator*(const ModInt &a) const { return (ModInt(*this) *= a); }
  ModInt operator-() const { return ModInt(-x); }
  ModInt pow(long long e) const {
    ModInt x2 = x, xe = 1;
    for (; e; e >>= 1) {
      if (e & 1) xe *= x2;
      x2 *= x2;
    }
    return xe;
  }
  ModInt inv() const {
    int a = x, b = M, y = 1, z = 0, t;
    for (; ; ) {
      t = a / b; a -= t * b;
      if (a == 0) {
        assert(b == 1 || b == -1);
        return ModInt(b * z);
      }
      y -= t * z;
      t = b / a; b -= t * a;
      if (b == 0) {
        assert(a == 1 || a == -1);
        return ModInt(a * y);
      }
      z -= t * y;
    }
  }
  friend ModInt operator+(long long a, const ModInt &b) { return (ModInt(a) += b); }
  friend ModInt operator-(long long a, const ModInt &b) { return (ModInt(a) -= b); }
  friend ModInt operator*(long long a, const ModInt &b) { return (ModInt(a) *= b); }
  friend std::ostream &operator<<(std::ostream &os, const ModInt &a) { return os << a.x; }
};

// M: prime, G: primitive root
template <int M, int G, int K> struct Fft {
  using Mint = ModInt<M>;
  // 1, 1/4, 1/8, 3/8, 1/16, 5/16, 3/16, 7/16, ...
  Mint g[1 << (K - 1)];
  constexpr Fft() : g() {
    static_assert(K >= 2, "Fft: K >= 2 must hold");
    static_assert(!((M - 1) & ((1 << K) - 1)), "Fft: 2^K | M - 1 must hold");
    g[0] = 1;
    g[1 << (K - 2)] = Mint(G).pow((M - 1) >> K);
    for (int l = 1 << (K - 2); l >= 2; l >>= 1) {
      g[l >> 1] = g[l] * g[l];
    }
    assert((g[1] * g[1]).x == M - 1);
    for (int l = 2; l <= 1 << (K - 2); l <<= 1) {
      for (int i = 1; i < l; ++i) {
        g[l + i] = g[l] * g[i];
      }
    }
  }
  void fft(vector<Mint> &x) const {
    const int n = x.size();
    assert(!(n & (n - 1)) && n <= 1 << K);
    for (int l = n; l >>= 1; ) {
      for (int i = 0; i < (n >> 1) / l; ++i) {
        for (int j = (i << 1) * l; j < ((i << 1) + 1) * l; ++j) {
          const Mint t = g[i] * x[j | l];
          x[j | l] = x[j] - t;
          x[j] += t;
        }
      }
    }
    for (int i = 0, j = 0; i < n; ++i) {
      if (i < j) std::swap(x[i], x[j]);
      for (int l = n; (l >>= 1) && !((j ^= l) & l); ) {}
    }
  }
};

constexpr int MO = 998244353;
constexpr int LIM = (1 << 20) + 1;
const Fft<MO, 3, 20> FFT;
using Mint = ModInt<MO>;

Mint inv[LIM];
struct ModIntPreparator {
  ModIntPreparator() {
    inv[1] = 1;
    for (int i = 2; i < LIM; ++i) inv[i] = -(MO / i) * inv[MO % i];
  }
} preparator;

struct Poly : public vector<Mint> {
  Poly() {}
  explicit Poly(int n) : vector<Mint>(n) {}
  Poly(const vector<Mint> &vec) : vector<Mint>(vec) {}
  Poly(std::initializer_list<Mint> il) : vector<Mint>(il) {}
  int size() const { return vector<Mint>::size(); }
  Poly take(int n) const { return Poly(vector<Mint>(this->begin(), this->begin() + min(max(n, 1), size()))); }
  friend std::ostream &operator<<(std::ostream &os, const Poly &f) {
    os << "[";
    for (int i = 0; i < f.size(); ++i) {
      if (i > 0) os << ", ";
      os << f[i];
    }
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
  Poly &operator*=(const Poly &f) {
    const int nt = size(), nf = f.size();
    int nn;
    for (nn = 1; nn < nt + nf - 1; nn <<= 1) {}
    Poly ff = f;
    resize(nn);
    ff.resize(nn);
    FFT.fft(*this);
    FFT.fft(ff);
    for (int i = 0; i < nn; ++i) (*this)[i] *= ff[i] * inv[nn];
    std::reverse(begin() + 1, end());
    FFT.fft(*this);
    resize(nt + nf - 1);
    return *this;
  }
  Poly &operator*=(const Mint &a) {
    for (int i = 0; i < size(); ++i) (*this)[i] *= a;
    return *this;
  }
  Poly operator+(const Poly &f) const { return (Poly(*this) += f); }
  Poly operator-(const Poly &f) const { return (Poly(*this) -= f); }
  Poly operator*(const Poly &f) const { return (Poly(*this) *= f); }
  Poly operator*(const Mint &a) const { return (Poly(*this) *= a); }
  friend Poly operator*(const Mint &a, const Poly &f) { return f * a; }

  Poly square(int n) const {
    const int nt = size();
    int nn;
    for (nn = 1; nn < nt + nt - 1; nn <<= 1) {}
    Poly f = *this;
    f.resize(nn);
    FFT.fft(f);
    for (int i = 0; i < nn; ++i) f[i] *= f[i] * inv[nn];
    std::reverse(f.begin() + 1, f.end());
    FFT.fft(f);
    f.resize(nt + nt - 1);
    return f;
  }

  Poly differential() const {
    Poly f(max(size() - 1, 1));
    for (int i = 1; i < size(); ++i) f[i - 1] = i * (*this)[i];
    return f;
  }

  Poly integral() const {
    Poly f(size() + 1);
    for (int i = 0; i < size(); ++i) f[i + 1] = inv[i + 1] * (*this)[i];
    return f;
  }

  Poly exp(int n) const {
    assert((*this)[0].x == 0);
    const Poly d = differential();
    Poly f = {1}, g = {1};
    for (int m = 1; m < n; m <<= 1) {
      g = g + g - (f * g.square(m)).take(m);
      Poly h = d.take(m - 1);
      h += (g * (f.differential() - f * h)).take(2 * m - 1);
      f += (f * (take(2 * m) - h.integral())).take(2 * m);
    }
    return f.take(n);
  }
};

// !!!Modify LIM and FFT!!!

// https://judge.yosupo.jp/problem/convolution_mod
void yosupo_convolution_mod() {
  int L, M;
  for (; ~scanf("%d%d", &L, &M); ) {
    Poly A(L), B(M);
    for (int i = 0; i < L; ++i) {
      scanf("%d", &A[i].x);
    }
    for (int i = 0; i < M; ++i) {
      scanf("%d", &B[i].x);
    }

    const Poly ans = A * B;
    for (int i = 0; i < ans.size(); ++i) {
      if (i > 0) printf(" ");
      printf("%d", ans[i].x);
    }
    puts("");
  }
}

// https://judge.yosupo.jp/problem/exp_of_formal_power_series
void yosupo_exp_of_formal_power_series() {
  int N;
  for (; ~scanf("%d", &N); ) {
    Poly A(N);
    for (int i = 0; i < N; ++i) {
      scanf("%d", &A[i].x);
    }

    const Poly ans = A.exp(N);
    for (int i = 0; i < ans.size(); ++i) {
      if (i > 0) printf(" ");
      printf("%d", ans[i].x);
    }
    puts("");
  }
}

int main() {
  // yosupo_convolution_mod();
  yosupo_exp_of_formal_power_series();
  return 0;
}
