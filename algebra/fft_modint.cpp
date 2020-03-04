#include <assert.h>
#include <stdio.h>
#include <algorithm>
#include <iostream>
#include <vector>

using std::vector;

template<int M_> struct ModInt {
  static constexpr int M = M_;
  int x;
  constexpr ModInt() : x(0) {}
  constexpr ModInt(long long x_) : x(x_ % M) { if (x < 0) x += M; }
  ModInt &operator+=(const ModInt &a) { x += a.x; if (x >= M) x -= M; return *this; }
  ModInt &operator-=(const ModInt &a) { x -= a.x; if (x < 0) x += M; return *this; }
  ModInt &operator*=(const ModInt &a) { x = static_cast<int>((static_cast<long long>(x) * a.x) % M); return *this; }
  ModInt &operator/=(const ModInt &a) { return (*this *= a.inv()); }
  ModInt operator+(const ModInt &a) const { return (ModInt(*this) += a); }
  ModInt operator-(const ModInt &a) const { return (ModInt(*this) -= a); }
  ModInt operator*(const ModInt &a) const { return (ModInt(*this) *= a); }
  ModInt operator/(const ModInt &a) const { return (ModInt(*this) /= a); }
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
  Mint gs[1 << (K - 1)];
  constexpr Fft() : gs() {
    static_assert(K >= 2, "Fft: K >= 2 must hold");
    static_assert(!((M - 1) & ((1 << K) - 1)), "Fft: 2^K | M - 1 must hold");
    gs[0] = 1;
    gs[1 << (K - 2)] = Mint(G).pow((M - 1) >> K);
    for (int l = 1 << (K - 2); l >= 2; l >>= 1) {
      gs[l >> 1] = gs[l] * gs[l];
    }
    assert((gs[1] * gs[1]).x == M - 1);
    for (int l = 2; l <= 1 << (K - 2); l <<= 1) {
      for (int i = 1; i < l; ++i) {
        gs[l + i] = gs[l] * gs[i];
      }
    }
  }
  void fft(vector<Mint> &xs) const {
    const int n = xs.size();
    assert(!(n & (n - 1)) && n <= 1 << K);
    for (int l = n; l >>= 1; ) {
      for (int i = 0; i < (n >> 1) / l; ++i) {
        for (int j = (i << 1) * l; j < (i << 1 | 1) * l; ++j) {
          const Mint t = gs[i] * xs[j + l];
          xs[j + l] = xs[j] - t;
          xs[j] += t;
        }
      }
    }
  }
  void invFft(vector<Mint> &xs) const {
    const int n = xs.size();
    assert(!(n & (n - 1)) && n <= 1 << K);
    for (int l = 1; l < n; l <<= 1) {
      std::reverse(xs.begin() + l, xs.begin() + (l << 1));
    }
    for (int l = 1; l < n; l <<= 1) {
      for (int i = 0; i < (n >> 1) / l; ++i) {
        for (int j = (i << 1) * l; j < (i << 1 | 1) * l; ++j) {
          const Mint t = gs[i] * (xs[j] - xs[j + l]);
          xs[j] += xs[j + l];
          xs[j + l] = t;
        }
      }
    }
  }
  vector<Mint> convolute(const vector<Mint> &as, const vector<Mint> &bs) const {
    const int na = as.size(), nb = bs.size();
    int n;
    for (n = 1; n < na + nb - 1; n <<= 1) {}
    const Mint invN = Mint(n).inv();
    vector<Mint> xs(n, 0), ys(n, 0);
    std::copy(as.begin(), as.end(), xs.begin());
    std::copy(bs.begin(), bs.end(), ys.begin());
    fft(xs);
    fft(ys);
    for (int i = 0; i < n; ++i) xs[i] = xs[i] * ys[i] * invN;
    invFft(xs);
    xs.resize(na + nb - 1);
    return xs;
  }
};

constexpr int MO = 998244353;
const Fft<MO, 3, 20> FFT;
using Mint = ModInt<MO>;

// https://judge.yosupo.jp/problem/convolution_mod
int readInt() {
  int c;
  for (; ; ) {
    c = getchar();
    if ('0' <= c && c <= '9') break;
    if (c == -1) throw -1;
    if (c == '-') return -readInt();
  }
  int x = c - '0';
  for (; ; ) {
    c = getchar();
    if (!('0' <= c && c <= '9')) return x;
    x = x * 10 + (c - '0');
  }
}
char writeIntBuffer[10];
void writeInt(int x) {
  if (x < 0) {
    putchar('-');
    x = -x;
  }
  int i = 0;
  do {
    writeIntBuffer[i++] = '0' + (x % 10);
    x /= 10;
  } while (x != 0);
  for (; i > 0; ) {
    putchar(writeIntBuffer[--i]);
  }
}

int main() {
  try {
    for (; ; ) {
      const int L = readInt();
      const int M = readInt();
      vector<Mint> A(L), B(M);
      for (int i = 0; i < L; ++i) {
        A[i].x = readInt();
      }
      for (int i = 0; i < M; ++i) {
        B[i].x = readInt();
      }

      const vector<Mint> res = FFT.convolute(A, B);
      for (int i = 0; i < L + M - 1; ++i) {
        if (i > 0) putchar(' ');
        writeInt(res[i].x);
      }
      putchar('\n');
    }
  } catch (int) {
  }
  return 0;
}
