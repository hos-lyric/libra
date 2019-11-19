#include <assert.h>
#include <stdio.h>
#include <algorithm>
#include <vector>

using std::vector;

// M: prime, G: primitive root
template <int M, int G, int K> struct Fft {
  // 1, 1/4, 1/8, 3/8, 1/16, 5/16, 3/16, 7/16, ...
  int g[1 << (K - 1)];
  constexpr Fft() : g() {
    static_assert(K >= 2, "Fft: K >= 2 must hold");
    static_assert(!((M - 1) & ((1 << K) - 1)), "Fft: 2^K | M - 1 must hold");
    g[0] = 1;
    long long g2 = G, gg = 1;
    for (int e = (M - 1) >> K; e; e >>= 1) {
      if (e & 1) gg = (gg * g2) % M;
      g2 = (g2 * g2) % M;
    }
    g[1 << (K - 2)] = gg;
    for (int l = 1 << (K - 2); l >= 2; l >>= 1) {
      g[l >> 1] = (static_cast<long long>(g[l]) * g[l]) % M;
    }
    assert((static_cast<long long>(g[1]) * g[1]) % M == M - 1);
    for (int l = 2; l <= 1 << (K - 2); l <<= 1) {
      for (int i = 1; i < l; ++i) {
        g[l + i] = (static_cast<long long>(g[l]) * g[i]) % M;
      }
    }
  }
  void fft(vector<int> &x) const {
    const int n = x.size();
    assert(!(n & (n - 1)) && n <= 1 << K);
    for (int l = n; l >>= 1; ) {
      for (int i = 0; i < (n >> 1) / l; ++i) {
        for (int j = (i << 1) * l; j < (i << 1 | 1) * l; ++j) {
          const int t = (static_cast<long long>(g[i]) * x[j + l]) % M;
          if ((x[j + l] = x[j] - t) < 0) x[j + l] += M;
          if ((x[j] += t) >= M) x[j] -= M;
        }
      }
    }
    for (int i = 0, j = 0; i < n; ++i) {
      if (i < j) std::swap(x[i], x[j]);
      for (int l = n; (l >>= 1) && !((j ^= l) & l); ) {}
    }
  }
  vector<int> convolution(const vector<int> &a, const vector<int> &b) const {
    const int na = a.size(), nb = b.size();
    int n, invN = 1;
    for (n = 1; n < na + nb - 1; n <<= 1) invN = ((invN & 1) ? (invN + M) : invN) >> 1;
    vector<int> x(n, 0), y(n, 0);
    std::copy(a.begin(), a.end(), x.begin());
    std::copy(b.begin(), b.end(), y.begin());
    fft(x);
    fft(y);
    for (int i = 0; i < n; ++i) x[i] = (((static_cast<long long>(x[i]) * y[i]) % M) * invN) % M;
    std::reverse(x.begin() + 1, x.end());
    fft(x);
    x.resize(na + nb - 1);
    return x;
  }
};

const Fft<998244353, 3, 20> FFT;

void unittest() {
  constexpr Fft<97, 92, 5> FFT97;
  const vector<int> a{31, 41, 59, 26, 53};
  const vector<int> b{58, 9, 79, 32, 38, 46};
  const vector<int> c{52, 38, 32, 62, 80, 31, 29, 63, 9, 13};
  assert(FFT97.convolution(a, b) == c);
}


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


// https://judge.yosupo.jp/problem/convolution_mod
int main() {
  // unittest();

  try {
    for (; ; ) {
      const int L = readInt();
      const int M = readInt();
      vector<int> A(L), B(M);
      for (int i = 0; i < L; ++i) {
        A[i] = readInt();
      }
      for (int i = 0; i < M; ++i) {
        B[i] = readInt();
      }

      const vector<int> res = FFT.convolution(A, B);
      for (int i = 0; i < L + M - 1; ++i) {
        if (i > 0) putchar(' ');
        writeInt(res[i]);
      }
      putchar('\n');
    }
  } catch (int) {
  }
  return 0;
}
