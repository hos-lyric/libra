#include <assert.h>
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
  static constexpr unsigned G = G_;
  static constexpr int K = K_;
  ModInt<M> FFT_ROOTS[K + 1], INV_FFT_ROOTS[K + 1];
  ModInt<M> FFT_RATIOS[K], INV_FFT_RATIOS[K];
  Fft() {
    const ModInt<M> g(G);
    for (int k = 0; k <= K; ++k) {
      FFT_ROOTS[k] = g.pow((M - 1U) >> k);
      INV_FFT_ROOTS[k] = FFT_ROOTS[k].inv();
    }
    for (int k = 0; k <= K - 2; ++k) {
      FFT_RATIOS[k] = -g.pow(3U * ((M - 1U) >> (k + 2)));
      INV_FFT_RATIOS[k] = FFT_RATIOS[k].inv();
    }
    assert(FFT_ROOTS[1] == M - 1U);
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
      ModInt<M> prod = 1U;
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
        ModInt<M> prod = 1U;
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
        ModInt<M> prod = 1U;
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
      ModInt<M> prod = 1U;
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
      ModInt<M> prod = 1U;
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
  vector<ModInt<M>> square(vector<ModInt<M>> as) const {
    if (as.empty()) return {};
    const int len = as.size() + as.size() - 1;
    int n = 1;
    for (; n < len; n <<= 1) {}
    as.resize(n); fft(as);
    for (int i = 0; i < n; ++i) as[i] *= as[i];
    invFft(as);
    as.resize(len);
    return as;
  }
};

// M0 M1 M2 = 789204840662082423367925761 (> 7.892 * 10^26, > 2^89)
// M0 M3 M4 M5 M6 = 797766583174034668024539679147517452591562753 (> 7.977 * 10^44, > 2^149)
const Fft<998244353U, 3U, 23> FFT0;
const Fft<897581057U, 3U, 23> FFT1;
const Fft<880803841U, 26U, 23> FFT2;
const Fft<985661441U, 3U, 22> FFT3;
const Fft<943718401U, 7U, 22> FFT4;
const Fft<935329793U, 3U, 22> FFT5;
const Fft<918552577U, 5U, 22> FFT6;

// T = unsigned, unsigned long long, ModInt<M>
template <class T, unsigned M0, unsigned M1, unsigned M2>
T garner(ModInt<M0> a0, ModInt<M1> a1, ModInt<M2> a2) {
  static const ModInt<M1> INV_M0_M1 = ModInt<M1>(M0).inv();
  static const ModInt<M2> INV_M0M1_M2 = (ModInt<M2>(M0) * M1).inv();
  const ModInt<M1> b1 = INV_M0_M1 * (a1 - a0.x);
  const ModInt<M2> b2 = INV_M0M1_M2 * (a2 - (ModInt<M2>(b1.x) * M0 + a0.x));
  return (T(b2.x) * M1 + b1.x) * M0 + a0.x;
}
template <class T, unsigned M0, unsigned M1, unsigned M2, unsigned M3, unsigned M4>
T garner(ModInt<M0> a0, ModInt<M1> a1, ModInt<M2> a2, ModInt<M3> a3, ModInt<M4> a4) {
  static const ModInt<M1> INV_M0_M1 = ModInt<M1>(M0).inv();
  static const ModInt<M2> INV_M0M1_M2 = (ModInt<M2>(M0) * M1).inv();
  static const ModInt<M3> INV_M0M1M2_M3 = (ModInt<M3>(M0) * M1 * M2).inv();
  static const ModInt<M4> INV_M0M1M2M3_M4 = (ModInt<M4>(M0) * M1 * M2 * M3).inv();
  const ModInt<M1> b1 = INV_M0_M1 * (a1 - a0.x);
  const ModInt<M2> b2 = INV_M0M1_M2 * (a2 - (ModInt<M2>(b1.x) * M0 + a0.x));
  const ModInt<M3> b3 = INV_M0M1M2_M3 * (a3 - ((ModInt<M3>(b2.x) * M1 + b1.x) * M0 + a0.x));
  const ModInt<M4> b4 = INV_M0M1M2M3_M4 * (a4 - (((ModInt<M4>(b3.x) * M2 + b2.x) * M1 + b1.x) * M0 + a0.x));
  return (((T(b4.x) * M3 + b3.x) * M2 + b2.x) * M1 + b1.x) * M0 + a0.x;
}

template <unsigned M> vector<ModInt<M>> convolve(const vector<ModInt<M>> &as, const vector<ModInt<M>> &bs) {
  static constexpr unsigned M0 = decltype(FFT0)::M;
  static constexpr unsigned M1 = decltype(FFT1)::M;
  static constexpr unsigned M2 = decltype(FFT2)::M;
  if (as.empty() || bs.empty()) return {};
  const int asLen = as.size(), bsLen = bs.size();
  vector<ModInt<M0>> as0(asLen), bs0(bsLen);
  for (int i = 0; i < asLen; ++i) as0[i] = as[i].x;
  for (int i = 0; i < bsLen; ++i) bs0[i] = bs[i].x;
  const vector<ModInt<M0>> cs0 = FFT0.convolve(as0, bs0);
  vector<ModInt<M1>> as1(asLen), bs1(bsLen);
  for (int i = 0; i < asLen; ++i) as1[i] = as[i].x;
  for (int i = 0; i < bsLen; ++i) bs1[i] = bs[i].x;
  const vector<ModInt<M1>> cs1 = FFT1.convolve(as1, bs1);
  vector<ModInt<M2>> as2(asLen), bs2(bsLen);
  for (int i = 0; i < asLen; ++i) as2[i] = as[i].x;
  for (int i = 0; i < bsLen; ++i) bs2[i] = bs[i].x;
  const vector<ModInt<M2>> cs2 = FFT2.convolve(as2, bs2);
  vector<ModInt<M>> cs(asLen + bsLen - 1);
  for (int i = 0; i < asLen + bsLen - 1; ++i) {
    cs[i] = garner<ModInt<M>>(cs0[i], cs1[i], cs2[i]);
  }
  return cs;
}
template <unsigned M> vector<ModInt<M>> square(const vector<ModInt<M>> &as) {
  static constexpr unsigned M0 = decltype(FFT0)::M;
  static constexpr unsigned M1 = decltype(FFT1)::M;
  static constexpr unsigned M2 = decltype(FFT2)::M;
  if (as.empty()) return {};
  const int asLen = as.size();
  vector<ModInt<M0>> as0(asLen);
  for (int i = 0; i < asLen; ++i) as0[i] = as[i].x;
  const vector<ModInt<M0>> cs0 = FFT0.square(as0);
  vector<ModInt<M1>> as1(asLen);
  for (int i = 0; i < asLen; ++i) as1[i] = as[i].x;
  const vector<ModInt<M1>> cs1 = FFT1.square(as1);
  vector<ModInt<M2>> as2(asLen);
  for (int i = 0; i < asLen; ++i) as2[i] = as[i].x;
  const vector<ModInt<M2>> cs2 = FFT2.square(as2);
  vector<ModInt<M>> cs(asLen + asLen - 1);
  for (int i = 0; i < asLen + asLen - 1; ++i) {
    cs[i] = garner<ModInt<M>>(cs0[i], cs1[i], cs2[i]);
  }
  return cs;
}

// mod 2^64
vector<unsigned long long> convolve(const vector<unsigned long long> &as, const vector<unsigned long long> &bs) {
  static constexpr unsigned M0 = decltype(FFT0)::M;
  static constexpr unsigned M3 = decltype(FFT3)::M;
  static constexpr unsigned M4 = decltype(FFT4)::M;
  static constexpr unsigned M5 = decltype(FFT5)::M;
  static constexpr unsigned M6 = decltype(FFT6)::M;
  if (as.empty() || bs.empty()) return {};
  const int asLen = as.size(), bsLen = bs.size();
  vector<ModInt<M0>> as0(asLen), bs0(bsLen);
  for (int i = 0; i < asLen; ++i) as0[i] = as[i];
  for (int i = 0; i < bsLen; ++i) bs0[i] = bs[i];
  const vector<ModInt<M0>> cs0 = FFT0.convolve(as0, bs0);
  vector<ModInt<M3>> as3(asLen), bs3(bsLen);
  for (int i = 0; i < asLen; ++i) as3[i] = as[i];
  for (int i = 0; i < bsLen; ++i) bs3[i] = bs[i];
  const vector<ModInt<M3>> cs3 = FFT3.convolve(as3, bs3);
  vector<ModInt<M4>> as4(asLen), bs4(bsLen);
  for (int i = 0; i < asLen; ++i) as4[i] = as[i];
  for (int i = 0; i < bsLen; ++i) bs4[i] = bs[i];
  const vector<ModInt<M4>> cs4 = FFT4.convolve(as4, bs4);
  vector<ModInt<M5>> as5(asLen), bs5(bsLen);
  for (int i = 0; i < asLen; ++i) as5[i] = as[i];
  for (int i = 0; i < bsLen; ++i) bs5[i] = bs[i];
  const vector<ModInt<M5>> cs5 = FFT5.convolve(as5, bs5);
  vector<ModInt<M6>> as6(asLen), bs6(bsLen);
  for (int i = 0; i < asLen; ++i) as6[i] = as[i];
  for (int i = 0; i < bsLen; ++i) bs6[i] = bs[i];
  const vector<ModInt<M6>> cs6 = FFT6.convolve(as6, bs6);
  vector<unsigned long long> cs(asLen + bsLen - 1);
  for (int i = 0; i < asLen + bsLen - 1; ++i) {
    cs[i] = garner<unsigned long long>(cs0[i], cs3[i], cs4[i], cs5[i], cs6[i]);
  }
  return cs;
}
vector<unsigned long long> square(const vector<unsigned long long> &as) {
  static constexpr unsigned M0 = decltype(FFT0)::M;
  static constexpr unsigned M3 = decltype(FFT3)::M;
  static constexpr unsigned M4 = decltype(FFT4)::M;
  static constexpr unsigned M5 = decltype(FFT5)::M;
  static constexpr unsigned M6 = decltype(FFT6)::M;
  if (as.empty()) return {};
  const int asLen = as.size();
  vector<ModInt<M0>> as0(asLen);
  for (int i = 0; i < asLen; ++i) as0[i] = as[i];
  const vector<ModInt<M0>> cs0 = FFT0.square(as0);
  vector<ModInt<M3>> as3(asLen);
  for (int i = 0; i < asLen; ++i) as3[i] = as[i];
  const vector<ModInt<M3>> cs3 = FFT3.square(as3);
  vector<ModInt<M4>> as4(asLen);
  for (int i = 0; i < asLen; ++i) as4[i] = as[i];
  const vector<ModInt<M4>> cs4 = FFT4.square(as4);
  vector<ModInt<M5>> as5(asLen);
  for (int i = 0; i < asLen; ++i) as5[i] = as[i];
  const vector<ModInt<M5>> cs5 = FFT5.square(as5);
  vector<ModInt<M6>> as6(asLen);
  for (int i = 0; i < asLen; ++i) as6[i] = as[i];
  const vector<ModInt<M6>> cs6 = FFT6.square(as6);
  vector<unsigned long long> cs(asLen + asLen - 1);
  for (int i = 0; i < asLen + asLen - 1; ++i) {
    cs[i] = garner<unsigned long long>(cs0[i], cs3[i], cs4[i], cs5[i], cs6[i]);
  }
  return cs;
}

// Results must be in [-448002610255888384, 448002611254132736].
// (> 4.480 * 10^17, > 2^58)
vector<long long> convolveSmall2(const vector<long long> &as, const vector<long long> &bs) {
  static constexpr unsigned M0 = decltype(FFT0)::M;
  static constexpr unsigned M1 = decltype(FFT1)::M;
  static const ModInt<M1> INV_M0_M1 = ModInt<M1>(M0).inv();
  if (as.empty() || bs.empty()) return {};
  const int asLen = as.size(), bsLen = bs.size();
  vector<ModInt<M0>> as0(asLen), bs0(bsLen);
  for (int i = 0; i < asLen; ++i) as0[i] = as[i];
  for (int i = 0; i < bsLen; ++i) bs0[i] = bs[i];
  const vector<ModInt<M0>> cs0 = FFT0.convolve(as0, bs0);
  vector<ModInt<M1>> as1(asLen), bs1(bsLen);
  for (int i = 0; i < asLen; ++i) as1[i] = as[i];
  for (int i = 0; i < bsLen; ++i) bs1[i] = bs[i];
  const vector<ModInt<M1>> cs1 = FFT1.convolve(as1, bs1);
  vector<long long> cs(asLen + bsLen - 1);
  for (int i = 0; i < asLen + bsLen - 1; ++i) {
    const ModInt<M1> d1 = INV_M0_M1 * (cs1[i] - cs0[i].x);
    cs[i] = (d1.x > M1 - d1.x)
        ? (-1ULL - (static_cast<unsigned long long>(M1 - 1U - d1.x) * M0 + (M0 - 1U - cs0[i].x)))
        : (static_cast<unsigned long long>(d1.x) * M0 + cs0[i].x);
  }
  return cs;
}
vector<long long> squareSmall2(const vector<long long> &as) {
  static constexpr unsigned M0 = decltype(FFT0)::M;
  static constexpr unsigned M1 = decltype(FFT1)::M;
  static const ModInt<M1> INV_M0_M1 = ModInt<M1>(M0).inv();
  if (as.empty()) return {};
  const int asLen = as.size();
  vector<ModInt<M0>> as0(asLen);
  for (int i = 0; i < asLen; ++i) as0[i] = as[i];
  const vector<ModInt<M0>> cs0 = FFT0.square(as0);
  vector<ModInt<M1>> as1(asLen);
  for (int i = 0; i < asLen; ++i) as1[i] = as[i];
  const vector<ModInt<M1>> cs1 = FFT1.square(as1);
  vector<long long> cs(asLen + asLen - 1);
  for (int i = 0; i < asLen + asLen - 1; ++i) {
    const ModInt<M1> d1 = INV_M0_M1 * (cs1[i] - cs0[i].x);
    cs[i] = (d1.x > M1 - d1.x)
        ? (-1ULL - (static_cast<unsigned long long>(M1 - 1U - d1.x) * M0 + (M0 - 1U - cs0[i].x)))
        : (static_cast<unsigned long long>(d1.x) * M0 + cs0[i].x);
  }
  return cs;
}

// Results must be in [-2^63, 2^63).
vector<long long> convolveSmall3(const vector<long long> &as, const vector<long long> &bs) {
  static constexpr unsigned M0 = decltype(FFT0)::M;
  static constexpr unsigned M1 = decltype(FFT1)::M;
  static constexpr unsigned M2 = decltype(FFT2)::M;
  static const ModInt<M1> INV_M0_M1 = ModInt<M1>(M0).inv();
  static const ModInt<M2> INV_M0M1_M2 = (ModInt<M2>(M0) * M1).inv();
  if (as.empty() || bs.empty()) return {};
  const int asLen = as.size(), bsLen = bs.size();
  vector<ModInt<M0>> as0(asLen), bs0(bsLen);
  for (int i = 0; i < asLen; ++i) as0[i] = as[i];
  for (int i = 0; i < bsLen; ++i) bs0[i] = bs[i];
  const vector<ModInt<M0>> cs0 = FFT0.convolve(as0, bs0);
  vector<ModInt<M1>> as1(asLen), bs1(bsLen);
  for (int i = 0; i < asLen; ++i) as1[i] = as[i];
  for (int i = 0; i < bsLen; ++i) bs1[i] = bs[i];
  const vector<ModInt<M1>> cs1 = FFT1.convolve(as1, bs1);
  vector<ModInt<M2>> as2(asLen), bs2(bsLen);
  for (int i = 0; i < asLen; ++i) as2[i] = as[i];
  for (int i = 0; i < bsLen; ++i) bs2[i] = bs[i];
  const vector<ModInt<M2>> cs2 = FFT2.convolve(as2, bs2);
  vector<long long> cs(asLen + bsLen - 1);
  for (int i = 0; i < asLen + bsLen - 1; ++i) {
    const ModInt<M1> d1 = INV_M0_M1 * (cs1[i] - cs0[i].x);
    const ModInt<M2> d2 = INV_M0M1_M2 * (cs2[i] - (ModInt<M2>(d1.x) * M0 + cs0[i].x));
    cs[i] = (d2.x > M2 - d2.x)
        ? (-1ULL - ((static_cast<unsigned long long>(M2 - 1U - d2.x) * M1 + (M1 - 1U - d1.x)) * M0 + (M0 - 1U - cs0[i].x)))
        : ((static_cast<unsigned long long>(d2.x) * M1 + d1.x) * M0 + cs0[i].x);
  }
  return cs;
}
vector<long long> squareSmall3(const vector<long long> &as) {
  static constexpr unsigned M0 = decltype(FFT0)::M;
  static constexpr unsigned M1 = decltype(FFT1)::M;
  static constexpr unsigned M2 = decltype(FFT2)::M;
  static const ModInt<M1> INV_M0_M1 = ModInt<M1>(M0).inv();
  static const ModInt<M2> INV_M0M1_M2 = (ModInt<M2>(M0) * M1).inv();
  if (as.empty()) return {};
  const int asLen = as.size();
  vector<ModInt<M0>> as0(asLen);
  for (int i = 0; i < asLen; ++i) as0[i] = as[i];
  const vector<ModInt<M0>> cs0 = FFT0.square(as0);
  vector<ModInt<M1>> as1(asLen);
  for (int i = 0; i < asLen; ++i) as1[i] = as[i];
  const vector<ModInt<M1>> cs1 = FFT1.square(as1);
  vector<ModInt<M2>> as2(asLen);
  for (int i = 0; i < asLen; ++i) as2[i] = as[i];
  const vector<ModInt<M2>> cs2 = FFT2.square(as2);
  vector<long long> cs(asLen + asLen - 1);
  for (int i = 0; i < asLen + asLen - 1; ++i) {
    const ModInt<M1> d1 = INV_M0_M1 * (cs1[i] - cs0[i].x);
    const ModInt<M2> d2 = INV_M0M1_M2 * (cs2[i] - (ModInt<M2>(d1.x) * M0 + cs0[i].x));
    cs[i] = (d2.x > M2 - d2.x)
        ? (-1ULL - ((static_cast<unsigned long long>(M2 - 1U - d2.x) * M1 + (M1 - 1U - d1.x)) * M0 + (M0 - 1U - cs0[i].x)))
        : ((static_cast<unsigned long long>(d2.x) * M1 + d1.x) * M0 + cs0[i].x);
  }
  return cs;
}
////////////////////////////////////////////////////////////////////////////////

void unittest() {
  {
    // const Fft<998244353, 2, 23> THIS_SHOULD_FAIL_IN_CONSTRUCTOR;
  }
  {
    assert(FFT0.FFT_ROOTS[23] == 15311432U);
    assert(FFT0.INV_FFT_ROOTS[23] == 469870224U);
    assert(FFT0.FFT_RATIOS[21] == 867605899U);
    assert(FFT0.INV_FFT_RATIOS[21] == 103369235U);
  }
  {
    const Fft<97, 92, 5> FFT;
    using Mint = ModInt<decltype(FFT)::M>;
    const vector<Mint> as{31, 41, 59, 26, 53};
    const vector<Mint> bs{58, 9, 79, 32, 38, 46};
    const vector<Mint> cs{52, 38, 32, 62, 80, 31, 29, 63, 9, 13};
    assert(FFT.convolve(as, bs) == cs);
  }
  {
    using Mint = ModInt<1000000007>;
    constexpr int asLen = 100, bsLen = 200;
    vector<Mint> as(asLen), bs(bsLen);
    for (int i = 0; i < asLen; ++i) as[i] = 1234567890ULL * i * i;
    for (int j = 0; j < bsLen; ++j) bs[j] = 2345678901ULL * j * j * j;
    vector<Mint> cs(asLen + bsLen - 1, 0);
    for (int i = 0; i < asLen; ++i) for (int j = 0; j < bsLen; ++j) {
      cs[i + j] += as[i] * bs[j];
    }
    assert(convolve(as, bs) == cs);
  }
  {
    using Mint = ModInt<1000000007>;
    constexpr int asLen = 100;
    vector<Mint> as(asLen);
    for (int i = 0; i < asLen; ++i) as[i] = 3456789012ULL * i * i;
    vector<Mint> cs(asLen + asLen - 1, 0);
    for (int i = 0; i < asLen; ++i) for (int j = 0; j < asLen; ++j) {
      cs[i + j] += as[i] * as[j];
    }
    assert(square(as) == cs);
  }
  {
    constexpr int asLen = 400, bsLen = 300;
    vector<unsigned long long> as(asLen), bs(bsLen);
    for (int i = 0; i < asLen; ++i) as[i] = 123456789012345678ULL * i * i;
    for (int j = 0; j < bsLen; ++j) bs[j] = 234567890123456781ULL * j * j * j;
    vector<unsigned long long> cs(asLen + bsLen - 1, 0);
    for (int i = 0; i < asLen; ++i) for (int j = 0; j < bsLen; ++j) {
      cs[i + j] += as[i] * bs[j];
    }
    assert(convolve(as, bs) == cs);
  }
  {
    constexpr int asLen = 400;
    vector<unsigned long long> as(asLen);
    for (int i = 0; i < asLen; ++i) as[i] = 345678901234567890ULL * i * i;
    vector<unsigned long long> cs(asLen + asLen - 1, 0);
    for (int i = 0; i < asLen; ++i) for (int j = 0; j < asLen; ++j) {
      cs[i + j] += as[i] * as[j];
    }
    assert(square(as) == cs);
  }
  {
    const vector<long long> as{1};
    const vector<long long> bs{
        -448002610255888384LL,
        -448002610255888383LL,
        -200000000000000000LL,
        -1LL,
        0LL,
        1LL,
        200000000000000000LL,
        448002611254132735LL,
        448002611254132736LL,
    };
    assert(convolveSmall2(as, bs) == bs);
  }
  {
    constexpr int asLen = 50, bsLen = 60;
    vector<long long> as(asLen), bs(bsLen);
    for (int i = 0; i < asLen; ++i) as[i] = i * i;
    for (int j = 0; j < bsLen; ++j) bs[j] = j * j * j;
    vector<long long> cs(asLen + bsLen - 1, 0);
    for (int i = 0; i < asLen; ++i) for (int j = 0; j < bsLen; ++j) {
      cs[i + j] += as[i] * bs[j];
    }
    assert(convolveSmall2(as, bs) == cs);
  }
  {
    constexpr int asLen = 70;
    vector<long long> as(asLen);
    for (int i = 0; i < asLen; ++i) as[i] = i * i;
    vector<long long> cs(asLen + asLen - 1, 0);
    for (int i = 0; i < asLen; ++i) for (int j = 0; j < asLen; ++j) {
      cs[i + j] += as[i] * as[j];
    }
    assert(squareSmall2(as) == cs);
  }
  {
    const vector<long long> as{1};
    const vector<long long> bs{
        -9223372036854775807LL - 1,
        -9223372036854775807LL,
        -5000000000000000000LL,
        -1LL,
        0LL,
        1LL,
        5000000000000000000LL,
        9223372036854775806LL,
        9223372036854775807LL,
    };
    assert(convolveSmall3(as, bs) == bs);
  }
  {
    const vector<long long> as{123456789LL, -234567890LL};
    const vector<long long> bs{-314159265LL, 358979323LL, 846264338LL};
    const vector<long long> cs{-38785094091500085LL, 118010110449974697LL,
                               20272055464952212LL, -198506440146906820LL};
    assert(convolveSmall3(as, bs) == cs);
  }
  {
    const vector<long long> as{-345678901LL, 456789012LL};
    const vector<long long> cs{119493902596567801LL, -315804647314071624LL,
                               208656201483936144LL};
    assert(squareSmall3(as) == cs);
  }
}

int main() {
  unittest();
  return 0;
}
