#include <assert.h>
#include <string.h>
#include <vector>

#include "modint.h"

using std::vector;

////////////////////////////////////////////////////////////////////////////////
// M: prime, G: primitive root, 2^K | M - 1
template <unsigned M_, unsigned G_, int K_> struct Fft {
  static_assert(2U <= M_, "Fft: 2 <= M must hold.");
  static_assert(M_ < 1U << 30, "Fft: M < 2^30 must hold.");
  static_assert(1 <= K_, "Fft: 1 <= K must hold.");
  static_assert(K_ < 30, "Fft: K < 30 must hold.");
  static_assert(!((M_ - 1U) & ((1U << K_) - 1U)), "Fft: 2^K | M - 1 must hold.");
  static constexpr unsigned M = M_;
  static constexpr unsigned M2 = 2U * M_;
  static constexpr ModInt<M> G = G_;
  static constexpr int K = K_;
  ModInt<M> FFT_ROOTS[K + 1], INV_FFT_ROOTS[K + 1], FFT_RATIOS[K - 1], INV_FFT_RATIOS[K - 1];
  Fft() {
    for (int k = 0; k <= K; ++k) {
      FFT_ROOTS[k] = G.pow((M - 1U) >> k);
      INV_FFT_ROOTS[k] = FFT_ROOTS[k].inv();
    }
    for (int k = 0; k <= K - 2; ++k) {
      FFT_RATIOS[k] = -G.pow(3U * ((M - 1U) >> (k + 2)));
      INV_FFT_RATIOS[k] = FFT_RATIOS[k].inv();
    }
    assert(FFT_ROOTS[1].x == M - 1U);
  }
  // as[rev(i)] <- \sum_j \zeta^(ij) as[j]
  void fft(ModInt<M> *as, int n) const {
    assert(!(n & (n - 1))); assert(1 <= n); assert(n <= 1 << K);
    int m = n;
    if (m >>= 1) {
      for (int i = 0; i < m; ++i) {
        const unsigned x = as[i + m].x;  // < M
        as[i + m].x = as[i].x + M - x;  // < 2 M
        as[i].x += x;  // < 2 M
      }
    }
    if (m >>= 1) {
      ModInt<M> prod = 1;
      for (int h = 0, i0 = 0; i0 < n; i0 += (m << 1)) {
        for (int i = i0; i < i0 + m; ++i) {
          const unsigned x = (prod * as[i + m]).x;  // < M
          as[i + m].x = as[i].x + M - x;  // < 3 M
          as[i].x += x;  // < 3 M
        }
        prod *= FFT_RATIOS[__builtin_ctz(++h)];
      }
    }
    for (; m; ) {
      if (m >>= 1) {
        ModInt<M> prod = 1;
        for (int h = 0, i0 = 0; i0 < n; i0 += (m << 1)) {
          for (int i = i0; i < i0 + m; ++i) {
            const unsigned x = (prod * as[i + m]).x;  // < M
            as[i + m].x = as[i].x + M - x;  // < 4 M
            as[i].x += x;  // < 4 M
          }
          prod *= FFT_RATIOS[__builtin_ctz(++h)];
        }
      }
      if (m >>= 1) {
        ModInt<M> prod = 1;
        for (int h = 0, i0 = 0; i0 < n; i0 += (m << 1)) {
          for (int i = i0; i < i0 + m; ++i) {
            const unsigned x = (prod * as[i + m]).x;  // < M
            as[i].x = (as[i].x >= M2) ? (as[i].x - M2) : as[i].x;  // < 2 M
            as[i + m].x = as[i].x + M - x;  // < 3 M
            as[i].x += x;  // < 3 M
          }
          prod *= FFT_RATIOS[__builtin_ctz(++h)];
        }
      }
    }
    for (int i = 0; i < n; ++i) {
      as[i].x = (as[i].x >= M2) ? (as[i].x - M2) : as[i].x;  // < 2 M
      as[i].x = (as[i].x >= M) ? (as[i].x - M) : as[i].x;  // < M
    }
  }
  // as[i] <- (1/n) \sum_j \zeta^(-ij) as[rev(j)]
  void invFft(ModInt<M> *as, int n) const {
    assert(!(n & (n - 1))); assert(1 <= n); assert(n <= 1 << K);
    int m = 1;
    if (m < n >> 1) {
      ModInt<M> prod = 1;
      for (int h = 0, i0 = 0; i0 < n; i0 += (m << 1)) {
        for (int i = i0; i < i0 + m; ++i) {
          const unsigned long long y = as[i].x + M - as[i + m].x;  // < 2 M
          as[i].x += as[i + m].x;  // < 2 M
          as[i + m].x = (prod.x * y) % M;  // < M
        }
        prod *= INV_FFT_RATIOS[__builtin_ctz(++h)];
      }
      m <<= 1;
    }
    for (; m < n >> 1; m <<= 1) {
      ModInt<M> prod = 1;
      for (int h = 0, i0 = 0; i0 < n; i0 += (m << 1)) {
        for (int i = i0; i < i0 + (m >> 1); ++i) {
          const unsigned long long y = as[i].x + M2 - as[i + m].x;  // < 4 M
          as[i].x += as[i + m].x;  // < 4 M
          as[i].x = (as[i].x >= M2) ? (as[i].x - M2) : as[i].x;  // < 2 M
          as[i + m].x = (prod.x * y) % M;  // < M
        }
        for (int i = i0 + (m >> 1); i < i0 + m; ++i) {
          const unsigned long long y = as[i].x + M - as[i + m].x;  // < 2 M
          as[i].x += as[i + m].x;  // < 2 M
          as[i + m].x = (prod.x * y) % M;  // < M
        }
        prod *= INV_FFT_RATIOS[__builtin_ctz(++h)];
      }
    }
    if (m < n) {
      for (int i = 0; i < m; ++i) {
        const unsigned y = as[i].x + M2 - as[i + m].x;  // < 4 M
        as[i].x += as[i + m].x;  // < 4 M
        as[i + m].x = y;  // < 4 M
      }
    }
    const ModInt<M> invN = ModInt<M>(n).inv();
    for (int i = 0; i < n; ++i) {
      as[i] *= invN;
    }
  }
  void fft(vector<ModInt<M>> &as) const {
    fft(as.data(), as.size());
  }
  void invFft(vector<ModInt<M>> &as) const {
    invFft(as.data(), as.size());
  }
  vector<ModInt<M>> convolve(vector<ModInt<M>> as, vector<ModInt<M>> bs) const {
    if (as.empty() || bs.empty()) return {};
    const int len = as.size() + bs.size() - 1;
    int n = 1;
    for (; n < len; n <<= 1) {}
    as.resize(n); fft(as);
    bs.resize(n); fft(bs);
    for (int i = 0; i < n; ++i) as[i] *= bs[i];
    invFft(as);
    as.resize(len);
    return as;
  }
};

const Fft<998244353, 3, 23> FFT998244353;

// TODO: convolve mod non-FFT-friendly or mod 2^64
////////////////////////////////////////////////////////////////////////////////

void unittest() {
  {
    assert(FFT998244353.FFT_ROOTS[23] == 15311432U);
    assert(FFT998244353.INV_FFT_ROOTS[23] == 469870224U);
    assert(FFT998244353.FFT_RATIOS[21] == 867605899U);
    assert(FFT998244353.INV_FFT_RATIOS[21] == 103369235U);
  }
  {
    const Fft<97, 92, 5> FFT;
    const vector<ModInt<FFT.M>> as{31, 41, 59, 26, 53};
    const vector<ModInt<FFT.M>> bs{58, 9, 79, 32, 38, 46};
    const vector<ModInt<FFT.M>> cs{52, 38, 32, 62, 80, 31, 29, 63, 9, 13};
    assert(FFT.convolve(as, bs) == cs);
  }
}

int main() {
  unittest();
  return 0;
}
