#include <assert.h>
#include <stdio.h>
#include <algorithm>
#include <vector>

using std::vector;

// M: prime, G: primitive root
template <int M, int G, int K> struct Fft {
  // 1, 1/4, 1/8, 3/8, 1/16, 5/16, 3/16, 7/16, ...
  int gs[1 << (K - 1)];
  constexpr Fft() : gs() {
    static_assert(2 <= K && K <= 30, "Fft: 2 <= K <= 30 must hold");
    static_assert(!((M - 1) & ((1 << K) - 1)), "Fft: 2^K | M - 1 must hold");
    gs[0] = 1;
    long long g2 = G, gg = 1;
    for (int e = (M - 1) >> K; e; e >>= 1) {
      if (e & 1) gg = (gg * g2) % M;
      g2 = (g2 * g2) % M;
    }
    gs[1 << (K - 2)] = gg;
    for (int l = 1 << (K - 2); l >= 2; l >>= 1) {
      gs[l >> 1] = (static_cast<long long>(gs[l]) * gs[l]) % M;
    }
    assert((static_cast<long long>(gs[1]) * gs[1]) % M == M - 1);
    for (int l = 2; l <= 1 << (K - 2); l <<= 1) {
      for (int i = 1; i < l; ++i) {
        gs[l + i] = (static_cast<long long>(gs[l]) * gs[i]) % M;
      }
    }
  }
  void fft(vector<int> &xs) const {
    const int n = xs.size();
    assert(!(n & (n - 1)) && n <= 1 << K);
    for (int l = n; l >>= 1; ) {
      for (int i = 0; i < (n >> 1) / l; ++i) {
        const long long g = gs[i];
        for (int j = (i << 1) * l; j < (i << 1 | 1) * l; ++j) {
          const int t = (g * xs[j + l]) % M;
          if ((xs[j + l] = xs[j] - t) < 0) xs[j + l] += M;
          if ((xs[j] += t) >= M) xs[j] -= M;
        }
      }
    }
  }
  void invFft(vector<int> &xs) const {
    const int n = xs.size();
    assert(!(n & (n - 1)) && n <= 1 << K);
    for (int l = 1; l < n; l <<= 1) {
      std::reverse(xs.begin() + l, xs.begin() + (l << 1));
    }
    for (int l = 1; l < n; l <<= 1) {
      for (int i = 0; i < (n >> 1) / l; ++i) {
        const long long g = gs[i];
        for (int j = (i << 1) * l; j < (i << 1 | 1) * l; ++j) {
          int t = (g * (xs[j] - xs[j + l])) % M;
          if (t < 0) t += M;
          if ((xs[j] += xs[j + l]) >= M) xs[j] -= M;
          xs[j + l] = t;
        }
      }
    }
  }
  template<class T>
  vector<T> convolute(const vector<T> &as, const vector<T> &bs) const {
    const int na = as.size(), nb = bs.size();
    int n, invN = 1;
    for (n = 1; n < na + nb - 1; n <<= 1) {
      invN = ((invN & 1) ? (invN + M) : invN) >> 1;
    }
    vector<int> xs(n, 0), ys(n, 0);
    for (int i = 0; i < na; ++i) if ((xs[i] = as[i] % M) < 0) xs[i] += M;
    for (int i = 0; i < nb; ++i) if ((ys[i] = bs[i] % M) < 0) ys[i] += M;
    fft(xs);
    fft(ys);
    for (int i = 0; i < n; ++i) {
      xs[i] = (((static_cast<long long>(xs[i]) * ys[i]) % M) * invN) % M;
    }
    invFft(xs);
    xs.resize(na + nb - 1);
    return xs;
  }
};

const Fft<998244353, 3, 20> FFT;

void unittest() {
  constexpr Fft<97, 92, 5> FFT97;
  const vector<int> a{31, 41, 59, 26, 53};
  const vector<int> b{58, 9, 79, 32, 38, 46};
  const vector<int> c{52, 38, 32, 62, 80, 31, 29, 63, 9, 13};
  assert(FFT97.convolute(a, b) == c);
}


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

      const vector<int> res = FFT.convolute(A, B);
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
