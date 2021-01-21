#include <initializer_list>
#include <ostream>

#include "modint.h"
#include "fft.h"

using std::vector;

constexpr int LIM_POLY = 1 << 20;
Mint polyWork0[LIM_POLY], polyWork1[LIM_POLY];

struct Poly : public vector<Mint> {
  Poly() {}
  explicit Poly(int n) : vector<Mint>(n) {}
  Poly(const vector<Mint> &vec) : vector<Mint>(vec) {}
  Poly(std::initializer_list<Mint> il) : vector<Mint>(il) {}
  int size() const { return vector<Mint>::size(); }
  Poly take(int n) const { return Poly(vector<Mint>(this->begin(), this->begin() + min(max(n, 1), size()))); }
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
};

/*
Mint inv[LIM];
struct ModIntPreparator {
  ModIntPreparator() {
    inv[1] = 1;
    for (int i = 2; i < LIM; ++i) inv[i] = -(MO / i) * inv[MO % i];
  }
} preparator;

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
*/
