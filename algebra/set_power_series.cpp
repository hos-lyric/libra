#include <assert.h>
#include <string.h>
#include <algorithm>
#include <vector>

using std::max;
using std::min;
using std::vector;

// !!!Watch out for stack overflow!!!
// Usage: SetMul<T, N>()(n, as, bs)
template <class T, int N> struct SetMul {
  T zas[1 << N][N + 1], zbs[1 << N][N + 1];
  vector<T> operator()(int n, const vector<T> &as, const vector<T> &bs) {
    assert(static_cast<int>(as.size()) == 1 << n);
    assert(static_cast<int>(bs.size()) == 1 << n);
    for (int h = 0; h < 1 << n; ++h) {
      for (int k = 0; k <= n; ++k) zas[h][k] = 0;
      zas[h][__builtin_popcount(h)] = as[h];
    }
    for (int h = 0; h < 1 << n; ++h) {
      for (int k = 0; k <= n; ++k) zbs[h][k] = 0;
      zbs[h][__builtin_popcount(h)] = bs[h];
    }
    rec(n, n, 0);
    vector<T> cs(1 << n);
    for (int h = 0; h < 1 << n; ++h) cs[h] = zas[h][__builtin_popcount(h)];
    return cs;
  }
  void rec(int n, int m, int h0) {
    const int pop0 = __builtin_popcount(h0);
    if (m) {
      --m;
      for (int h = h0; h < h0 + (1 << m); ++h) {
        const int pop = __builtin_popcount(h);
        for (int k = pop - pop0; k <= pop; ++k) zas[h | 1 << m][k] += zas[h][k];
        for (int k = pop - pop0; k <= pop; ++k) zbs[h | 1 << m][k] += zbs[h][k];
      }
      rec(n, m, h0);
      rec(n, m, h0 | 1 << m);
      for (int h = h0; h < h0 + (1 << m); ++h) {
        const int pop = __builtin_popcount(h);
        for (int k = pop; k <= min(2 * pop, pop + (n - m - pop0)); ++k) zas[h | 1 << m][k] -= zas[h][k];
      }
    } else {
      for (int k = min(2 * pop0, n); k >= pop0; --k) {
        T t = 0;
        for (int l = max(0, k - pop0); l <= min(pop0, k); ++l) t += zas[h0][l] * zbs[h0][k - l];
        zas[h0][k] = t;
      }
    }
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>

#include "modint.h"

using std::cerr;
using std::endl;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

constexpr unsigned MO = 1'000'000'007;
using Mint = ModInt<MO>;

void unittest_setMul() {
  {
    assert((SetMul<int, 3>()(3,
                             vector<int>{1, 2, 3, 4, 5, 6, 7, 8},
                             vector<int>{9, 10, 11, 12, 13, 14, 15, 16})) ==
           (vector<int>{9, 28, 38, 100, 58, 144, 172, 408}));
  }
  {
    constexpr int MAX_N = 10;
    SetMul<Mint, MAX_N> setMul;
    for (int n = 0; n <= MAX_N; ++n) {
      // garbage
      for (int h = 0; h < 1 << MAX_N; ++h) for (int k = 0; k <= MAX_N; ++k) setMul.zas[h][k] = xrand();
      for (int h = 0; h < 1 << MAX_N; ++h) for (int k = 0; k <= MAX_N; ++k) setMul.zbs[h][k] = xrand();
      //
      vector<Mint> as(1 << n), bs(1 << n);
      for (int h = 0; h < 1 << n; ++h) as[h] = xrand();
      for (int h = 0; h < 1 << n; ++h) bs[h] = xrand();
      vector<Mint> expected(1 << n, 0);
      for (int ha = 0; ha < 1 << n; ++ha) for (int hb = 0; hb < 1 << n; ++hb) {
        if (!(ha & hb)) {
          expected[ha | hb] += as[ha] * bs[hb];
        }
      }
      assert(setMul(n, as, bs) == expected);
    }
  }
}

int main() {
  unittest_setMul(); cerr << "PASSED unittest_setMul" << endl;
  return 0;
}
