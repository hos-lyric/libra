#include <assert.h>
#include <chrono>
#include <iostream>
#include <vector>

#include "fft998244353.h"

using std::cerr;
using std::endl;
using std::vector;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void unittest_fft() {
  for (int k = 0; k < 10; ++k) {
    cerr << "unittest_fft: k = " << k << endl;
    vector<int> rev(1 << k, 0);
    for (int i = 0; i < 1 << k; ++i) {
      for (int l = 0; l < k; ++l) {
        if ((i & 1 << l)) {
          rev[i] |= 1 << (k - 1 - l);
        }
      }
    }
    vector<Mint> as(1 << k);
    for (int i = 0; i < 1 << k; ++i) {
      as[i] = xrand();
    }
    vector<Mint> bs = as;
    fft(bs);
    for (int i = 0; i < 1 << k; ++i) {
      Mint sum = 0;
      for (int j = 0; j < 1 << k; ++j) {
        sum += FFT_ROOTS[k].pow(i * j) * as[j];
      }
      assert(sum == bs[rev[i]]);
    }
  }
}

void unittest_invFft() {
  for (int k = 0; k < 10; ++k) {
    cerr << "unittest_invFft: k = " << k << endl;
    vector<int> rev(1 << k, 0);
    for (int i = 0; i < 1 << k; ++i) {
      for (int l = 0; l < k; ++l) {
        if ((i & 1 << l)) {
          rev[i] |= 1 << (k - 1 - l);
        }
      }
    }
    vector<Mint> bs(1 << k);
    for (int i = 0; i < 1 << k; ++i) {
      bs[i] = xrand();
    }
    vector<Mint> as = bs;
    invFft(as);
    for (int i = 0; i < 1 << k; ++i) {
      Mint sum = 0;
      for (int j = 0; j < 1 << k; ++j) {
        sum += FFT_ROOTS[k].pow(-i * j) * bs[rev[j]];
      }
      sum /= (1 << k);
      assert(sum == as[i]);
    }
  }
}

void unittest_convolve() {
  assert((vector<Mint>{}) == convolve({}, {}));
  assert((vector<Mint>{}) == convolve({}, {1, 2, 3}));
  assert((vector<Mint>{}) == convolve({4, 5, 6}, {}));
  assert((vector<Mint>{63, 142, 157, 88}) == convolve({7, 8}, {9, 10, 11}));
  for (const auto &lens : {vector<int>{100, 1000}, vector<int>{1234, 123}}) {
    const int asLen = lens[0], bsLen = lens[1];
    vector<Mint> as(asLen), bs(bsLen);
    for (int i = 0; i < asLen; ++i) {
      as[i] = xrand();
    }
    for (int i = 0; i < bsLen; ++i) {
      bs[i] = xrand();
    }
    vector<Mint> cs(asLen + bsLen - 1);
    for (int i = 0; i < asLen; ++i) for (int j = 0; j < bsLen; ++j) {
      cs[i + j] += as[i] * bs[j];
    }
    assert(cs == convolve(as, bs));
  }
}

void solve(const int N, const unsigned expected) {
  static constexpr int NUM_CASES = 100;
  const auto timerBegin = std::chrono::high_resolution_clock::now();
  unsigned ans = 0;
  for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
    vector<Mint> as(N), bs(N);
    for (int i = 0; i < N; ++i) {
      as[i] = xrand();
      bs[i] = xrand();
    }
    const vector<Mint> cs = convolve(as, bs);
    assert(cs.size() == static_cast<size_t>(N + N - 1));
    for (int i = 0; i < N + N - 1; ++i) {
      ans ^= (cs[i].x + i);
    }
  }
  const auto timerEnd = std::chrono::high_resolution_clock::now();
  cerr << NUM_CASES << " cases, N = " << N << ": expected = " << expected
       << ", actual = " << ans << endl;
  cerr << std::chrono::duration_cast<std::chrono::milliseconds>(
      timerEnd - timerBegin).count() << " msec" << endl;
  assert(expected == ans);
}
void measurement() {
  solve(1, 752656504);
  solve(10, 379388382);
  solve(100, 393163138);
  solve(1000, 594939637);
  solve(10000, 886351275);
  solve(100000, 737124305);
  solve(1000000, 490935560);
  // 14105 msec @ DAIVRabbit
}

int main() {
  measurement();
  unittest_fft();
  unittest_invFft();
  unittest_convolve();
  return 0;
}
