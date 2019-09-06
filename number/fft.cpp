#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <algorithm>
#include <vector>

using std::vector;

template<class T> T modInv(T a, T m) {
  T b = m, x = 1, y = 0, t;
  for (; ; ) {
    t = a / b; a -= t * b;
    if (a == 0) {
      assert(b == 1 || b == -1);
      if (b == -1) y = -y;
      return (y < 0) ? (y + m) : y;
    }
    x -= t * y;
    t = b / a; b -= t * a;
    if (b == 0) {
      assert(a == 1 || a == -1);
      if (a == -1) x = -x;
      return (x < 0) ? (x + m) : x;
    }
    y -= t * x;
  }
}

// G: primitive 2^K-th root of unity
template<int32_t M, int K, int32_t G> struct FFT {
  int n, logN;
  int64_t invN;
  vector<int32_t> g;

  FFT(int n) : n(n) {
    assert(!(n & (n - 1)) && 4 <= n && n <= 1 << K);
    logN = __builtin_ctz(n);
    invN = modInv(n, M);
    g.resize(n + 1);
    g[0] = 1;
    g[1] = G;
    for (int h = K - logN; h--; ) g[1] = (static_cast<int64_t>(g[1]) * g[1]) % M;
    for (int i = 2; i <= n; ++i) g[i] = (static_cast<int64_t>(g[i - 1]) * g[1]) % M;
    assert(g[0] != g[n >> 1] && g[0] == g[n]);
    for (int i = 0, j = 0; i < n >> 1; ++i) {
      if (i < j) {
        std::swap(g[i], g[j]);
        std::swap(g[n - i], g[n - j]);
      }
      for (int l = n >> 1; (l >>= 1) && !((j ^= l) & l); ) {}
    }
  }

  void fft(vector<int32_t> &x, bool inverse) const {
    assert(x.size() == static_cast<size_t>(n));
    for (int h = logN; h--; ) {
      const int l = 1 << h;
      for (int i = 0; i < n >> 1 >> h; ++i) {
        const int64_t gI = g[inverse ? (n - i) : i];
        for (int j = i << 1 << h; j < ((i << 1) + 1) << h; ++j) {
          const int32_t t = (gI * x[j | l]) % M;
          if ((x[j | l] = x[j] - t) < 0) x[j | l] += M;
          if ((x[j] += t) >= M) x[j] -= M;
        }
      }
    }
    for (int i = 0, j = 0; i < n; ++i) {
      if (i < j) std::swap(x[i], x[j]);
      for (int l = n; (l >>= 1) && !((j ^= l) & l); ) {}
    }
    if (inverse) for (int i = 0; i < n; ++i) x[i] = (invN * x[i]) % M;
  }

  template<class T> vector<T> convolution(const vector<T> &a, const vector<T> &b) {
    const int na = a.size(), nb = b.size();
    assert(na <= n && nb <= n);
    vector<int32_t> x(n, 0), y(n, 0);
    for (int i = 0; i < na; ++i) x[i] = a[i] % M;
    for (int i = 0; i < nb; ++i) y[i] = b[i] % M;
    fft(x, false);
    fft(y, false);
    for (int i = 0; i < n; ++i) x[i] = (static_cast<int64_t>(x[i]) * y[i]) % M;
    fft(x, true);
    const int nc = std::min(na + nb - 1, n);
    vector<T> c(nc);
    for (int i = 0; i < nc; ++i) c[i] = x[i];
    return c;
  }
};

void unittest() {
  FFT<97, 5, 28> fft(8);
  const vector<long long> a{31, 41, 59, 26, 53};
  const vector<long long> b{58, 97, 93, 23, 84, 62};
  const vector<long long> c{5, 38, 0, 20, 80, 23, 27, 77};
  assert(fft.convolution(a, b) == c);
}

// https://judge.yosupo.jp/problem/convolution_mod
int main() {
  // unittest();

  int L, M;
  for (; ~scanf("%d%d", &L, &M); ) {
    vector<int> A(L), B(M);
    for (int i = 0; i < L; ++i) {
      scanf("%d", &A[i]);
    }
    for (int i = 0; i < M; ++i) {
      scanf("%d", &B[i]);
    }

    int n;
    for (n = 4; n < L + M; n <<= 1) {}
    FFT<998244353, 23, 31> fft(n);
    const vector<int> res = fft.convolution(A, B);
    for (int i = 0; i < L + M - 1; ++i) {
      if (i > 0) printf(" ");
      printf("%d", res[i]);
    }
    puts("");
  }
  return 0;
}
