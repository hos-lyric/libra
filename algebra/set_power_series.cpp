#include <assert.h>
#include <string.h>
#include <algorithm>
#include <vector>

using std::max;
using std::min;
using std::vector;

// !!!Watch out for stack overflow!!!
template <class T, int N> struct SetMul {
  // Except for mul, these are enough for n <= N + 1.
  T zas[1 << N][N + 1], zbs[1 << N][N + 1];

  // as * bs
  // O(2^n n^2) time
  vector<T> operator()(int n, const vector<T> &as, const vector<T> &bs) {
    return mul(n, as, bs);
  }
  vector<T> mul(int n, const vector<T> &as, const vector<T> &bs) {
    assert(0 <= n); assert(n <= N);
    assert(static_cast<int>(as.size()) == 1 << n);
    assert(static_cast<int>(bs.size()) == 1 << n);
    vector<T> cs(1 << n);
    mul(n, as.data(), bs.data(), cs.data());
    return cs;
  }
  void mul(int n, const T *as, const T *bs, T *cs) {
    for (int h = 0; h < 1 << n; ++h) {
      for (int k = 0; k <= n; ++k) zas[h][k] = 0;
      zas[h][__builtin_popcount(h)] = as[h];
    }
    for (int h = 0; h < 1 << n; ++h) {
      for (int k = 0; k <= n; ++k) zbs[h][k] = 0;
      zbs[h][__builtin_popcount(h)] = bs[h];
    }
    rec(n, n, 0);
    for (int h = 0; h < 1 << n; ++h) cs[h] = zas[h][__builtin_popcount(h)];
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

  // exp(as)
  //   Assumes as[0] = 0.
  //   exp(a0 + a1 x) = exp(a0) + exp(a0) a1 x
  // O(2^n n^2) time
  vector<T> exp(int n, const vector<T> &as) {
    assert(0 <= n); assert(n <= N + 1);
    assert(static_cast<int>(as.size()) == 1 << n);
    vector<T> bs(1 << n);
    exp(n, as.data(), bs.data());
    return bs;
  }
  void exp(int n, const T *as, T *bs) {
    assert(!as[0]);
    bs[0] = 1;
    for (int m = 0; m < n; ++m) mul(m, bs, as + (1 << m), bs + (1 << m));
  }

  // \sum[0<=i<=n] fs[i] as^i/i!
  //   Assumes as[0] = 0.
  //   f(a0 + a1 x) = f(a0) + f'(a0) a1 x
  // O(2^n n^2) time
  vector<T> com(int n, const vector<T> &fs, const vector<T> &as) {
    assert(0 <= n); assert(n <= N + 1);
    assert(static_cast<int>(as.size()) == 1 << n);
    vector<T> bs(1 << n);
    com(fs.size(), n, fs.data(), as.data(), bs.data());
    return bs;
  }
  void com(int fsLen, int n, const T *fs, const T *as, T *bs) {
    assert(!as[0]);
    for (int i = n; i >= 0; --i) {
      for (int m = n - i; --m >= 0; ) mul(m, bs, as + (1 << m), bs + (1 << m));
      bs[0] = (i < fsLen) ? fs[i] : 0;
    }
  }

  // [x^[n]] as bs^i/i!  for 0 <= i <= n
  //   Assumes bs[0] = 0
  // O(2^n n^2) time
  vector<T> powProj(int n, vector<T> as, const vector<T> &bs) {
    assert(0 <= n); assert(n <= N + 1);
    assert(static_cast<int>(as.size()) == 1 << n);
    assert(static_cast<int>(bs.size()) == 1 << n);
    assert(!bs[0]);
    vector<T> cs(1 << max(n - 1, 0));
    vector<T> fs(n + 1);
    for (int i = 0; i <= n; ++i) {
      fs[i] = as[(1 << n) - 1];
      as[(1 << n) - 1] = 0;
      for (int m = 0; m < n - i; ++m) {
        mul(m, as.data() + ((1 << n) - (1 << (m + 1))), bs.data() + (1 << m), cs.data());
        for (int h = 0; h < 1 << m; ++h) as[(1 << n) - (1 << m) + h] += cs[h];
        for (int h = 0; h < 1 << m; ++h) as[(1 << n) - (1 << (m + 1)) + h] = 0;
      }
    }
    return fs;
  }

  // [x^[n]] as bs^i  for 0 <= i <= m
  //   not necessarily as[0] = 0
  // O(|fs| n + 2^n n^2) time
  vector<T> comPoly(int n, vector<T> fs, vector<T> as) {
    assert(0 <= n); assert(n <= N + 1);
    assert(static_cast<int>(as.size()) == 1 << n);
    const int fsLen = fs.size();
    if (fsLen == 0) return vector<T>(1 << n, 0);
    vector<T> gs(n + 1, 0);
    for (int i = 0; i <= n; ++i) {
      for (int j = fsLen; --j >= 0; ) (gs[i] *= as[0]) += fs[j];
      for (int j = 1; j < fsLen; ++j) fs[j - 1] = j * fs[j];
      fs[fsLen - 1] = 0;
    }
    as[0] = 0;
    return com(n, gs, as);
  }

  // [x^[n]] as bs^i  for 0 <= i < len
  //   not necessarily as[0] = 0
  // O(len n + 2^n n^2) time
  vector<T> powProjPoly(int n, const vector<T> &as, vector<T> bs, int len) {
    assert(0 <= n); assert(n <= N + 1);
    assert(static_cast<int>(as.size()) == 1 << n);
    assert(static_cast<int>(bs.size()) == 1 << n);
    assert(0 <= len);
    const T b = bs[0];
    bs[0] = 0;
    const auto gs = powProj(n, as, bs);
    vector<T> fs(len, 0), hs(n + 1, 0);
    hs[0] = 1;
    for (int i = 0; i < len; ++i) {
      for (int j = 0; j <= n; ++j) fs[i] += hs[j] * gs[j];
      for (int j = n; --j >= 0; ) hs[j + 1] = hs[j] * (i + 1);
      hs[0] *= b;
    }
    return fs;
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <random>

#include "modint.h"

using std::cerr;
using std::endl;
using std::mt19937_64;

constexpr unsigned MO = 1'000'000'007;
using Mint = ModInt<MO>;

vector<Mint> mulBrute(int n, const vector<Mint> &as, const vector<Mint> &bs) {
  assert(static_cast<int>(as.size()) == 1 << n);
  assert(static_cast<int>(bs.size()) == 1 << n);
  vector<Mint> cs(1 << n, 0);
  for (int ha = 0; ha < 1 << n; ++ha) for (int hb = 0; hb < 1 << n; ++hb) if (!(ha & hb)) {
    cs[ha | hb] += as[ha] * bs[hb];
  }
  return cs;
}

void unittest_setMul() {
  assert((SetMul<int, 0>()(0, vector<int>{5}, vector<int>{-8})) ==
         (vector<int>{-40}));
  assert((SetMul<int, 3>()(3,
                           vector<int>{1, 2, 3, 4, 5, 6, 7, 8},
                           vector<int>{9, 10, 11, 12, 13, 14, 15, 16})) ==
         (vector<int>{9, 28, 38, 100, 58, 144, 172, 408}));
  {
    constexpr int MAX_N = 10;
    mt19937_64 rng;
    SetMul<Mint, MAX_N> setMul;
    for (int n = 0; n <= MAX_N; ++n) {
      // put garbage
      for (int h = 0; h < 1 << MAX_N; ++h) for (int k = 0; k <= MAX_N; ++k) setMul.zas[h][k] = static_cast<unsigned long long>(rng());
      for (int h = 0; h < 1 << MAX_N; ++h) for (int k = 0; k <= MAX_N; ++k) setMul.zbs[h][k] = static_cast<unsigned long long>(rng());
      vector<Mint> as(1 << n), bs(1 << n);
      for (int h = 0; h < 1 << n; ++h) as[h] = static_cast<unsigned long long>(rng());
      for (int h = 0; h < 1 << n; ++h) bs[h] = static_cast<unsigned long long>(rng());
      const auto expected = mulBrute(n, as, bs);
      assert(setMul(n, as, bs) == expected);
    }
  }
}

void unittest_setExp() {
  assert((SetMul<int, 0>().exp(0, vector<int>{0})) ==
         (vector<int>{1}));
  assert((SetMul<int, 2>().exp(3, vector<int>{0, 2, 3, 5, 7, 11, 13, 17})) ==
         (vector<int>{1, 2, 3, 11, 7, 25, 34, 153}));
  {
    constexpr int MAX_N = 10;
    mt19937_64 rng;
    SetMul<Mint, MAX_N - 1> setMul;
    for (int n = 0; n <= MAX_N; ++n) {
      // put garbage
      for (int h = 0; h < 1 << (MAX_N - 1); ++h) for (int k = 0; k <= MAX_N - 1; ++k) setMul.zas[h][k] = static_cast<unsigned long long>(rng());
      for (int h = 0; h < 1 << (MAX_N - 1); ++h) for (int k = 0; k <= MAX_N - 1; ++k) setMul.zbs[h][k] = static_cast<unsigned long long>(rng());
      vector<Mint> as(1 << n, 0);
      for (int h = 1; h < 1 << n; ++h) as[h] = static_cast<unsigned long long>(rng());
      vector<Mint> expected(1 << n, 0);
      for (int i = n; i >= 0; --i) {
        expected = mulBrute(n, as, expected);
        Mint fac = 1;
        for (int j = 1; j <= i; ++j) fac *= j;
        expected[0] += fac.inv();
      }
      assert(setMul.exp(n, as) == expected);
    }
  }
}

void unittest_setCom() {
  assert((SetMul<int, 0>().com(0, vector<int>{58, 47}, vector<int>{0})) ==
         (vector<int>{58}));
  assert((SetMul<int, 3>().com(3,
                               vector<int>{10, 1000, 100000, 10000000},
                               vector<int>{0, 2, 3, 5, 7, 11, 13, 17})) ==
         (vector<int>{       10,
                           2000,
                           3000,
                         605000,
                           7000,
                        1411000,
                        2113000,
                      429417000}));
  {
    constexpr int MAX_N = 10;
    constexpr int MAX_M = 15;
    mt19937_64 rng;
    SetMul<Mint, MAX_N - 1> setMul;
    for (int n = 0; n <= MAX_N; ++n) for (int m = 0; m <= MAX_M; ++m) {
      // put garbage
      for (int h = 0; h < 1 << (MAX_N - 1); ++h) for (int k = 0; k <= MAX_N - 1; ++k) setMul.zas[h][k] = static_cast<unsigned long long>(rng());
      for (int h = 0; h < 1 << (MAX_N - 1); ++h) for (int k = 0; k <= MAX_N - 1; ++k) setMul.zbs[h][k] = static_cast<unsigned long long>(rng());
      vector<Mint> fs(m), as(1 << n, 0);
      for (int i = 0; i < m; ++i) fs[i] = static_cast<unsigned long long>(rng());
      for (int h = 1; h < 1 << n; ++h) as[h] = static_cast<unsigned long long>(rng());
      vector<Mint> expected(1 << n, 0);
      for (int i = m; --i >= 0; ) {
        expected = mulBrute(n, as, expected);
        Mint fac = 1;
        for (int j = 1; j <= i; ++j) fac *= j;
        expected[0] += fs[i] * fac.inv();
      }
      assert(setMul.com(n, fs, as) == expected);
    }
  }
}

void unittest_setPowProj() {
  assert((SetMul<int, 0>().powProj(0, vector<int>{-10}, vector<int>{0})) ==
         (vector<int>{-10}));
  assert((SetMul<int, 3>().powProj(3,
                                   vector<int>{-2, -3, -4, -5, -6, -7, -8, -9},
                                   vector<int>{0, 1, 1, 2, 2, 3, 3, 4})) ==
         (vector<int>{-9, -66, -40, -4}));
  {
    constexpr int MAX_N = 10;
    constexpr int MAX_M = 15;
    mt19937_64 rng;
    SetMul<Mint, MAX_N - 1> setMul;
    for (int n = 0; n <= MAX_N; ++n) for (int m = 0; m <= MAX_M; ++m) {
      // put garbage
      for (int h = 0; h < 1 << (MAX_N - 1); ++h) for (int k = 0; k <= MAX_N - 1; ++k) setMul.zas[h][k] = static_cast<unsigned long long>(rng());
      for (int h = 0; h < 1 << (MAX_N - 1); ++h) for (int k = 0; k <= MAX_N - 1; ++k) setMul.zbs[h][k] = static_cast<unsigned long long>(rng());
      vector<Mint> as(1 << n), bs(1 << n, 0);
      for (int h = 0; h < 1 << n; ++h) as[h] = static_cast<unsigned long long>(rng());
      for (int h = 1; h < 1 << n; ++h) bs[h] = static_cast<unsigned long long>(rng());
      vector<Mint> expected(n + 1, 0);
      auto cs = as;
      for (int i = 0; i <= n; ++i) {
        expected[i] = cs[(1 << n) - 1];
        cs = mulBrute(n, cs, bs);
        for (int h = 0; h < 1 << n; ++h) cs[h] /= (i + 1);
      }
      assert(setMul.powProj(n, as, bs) == expected);
    }
  }
}

void unittest_setComPoly() {
  assert((SetMul<int, 0>().comPoly(0, vector<int>{}, vector<int>{2})) ==
         (vector<int>{0}));
  assert((SetMul<int, 2>().comPoly(2,
                                   vector<int>{7, 1, 10, 1000, 1000000},
                                   vector<int>{2, 3, 5, 1})) ==
         (vector<int>{ 16008049,
                       96036123,
                      160060205,
                      752192341}));
  {
    constexpr int MAX_N = 10;
    constexpr int MAX_M = 15;
    mt19937_64 rng;
    SetMul<Mint, MAX_N - 1> setMul;
    for (int n = 0; n <= MAX_N; ++n) for (int m = 0; m <= MAX_M; ++m) {
      // put garbage
      for (int h = 0; h < 1 << (MAX_N - 1); ++h) for (int k = 0; k <= MAX_N - 1; ++k) setMul.zas[h][k] = static_cast<unsigned long long>(rng());
      for (int h = 0; h < 1 << (MAX_N - 1); ++h) for (int k = 0; k <= MAX_N - 1; ++k) setMul.zbs[h][k] = static_cast<unsigned long long>(rng());
      vector<Mint> fs(m), as(1 << n);
      for (int i = 0; i < m; ++i) fs[i] = static_cast<unsigned long long>(rng());
      for (int h = 0; h < 1 << n; ++h) as[h] = static_cast<unsigned long long>(rng());
      vector<Mint> expected(1 << n, 0);
      for (int i = m; --i >= 0; ) {
        expected = mulBrute(n, as, expected);
        expected[0] += fs[i];
      }
      assert(setMul.comPoly(n, fs, as) == expected);
    }
  }
}

void unittest_setPowProjPoly() {
  assert((SetMul<int, 0>().powProjPoly(0, vector<int>{2}, vector<int>{3}, 0)) ==
         (vector<int>{}));
  assert((SetMul<int, 2>().powProjPoly(2,
                                       vector<int>{1, 1000, 1000000, 100000000},
                                       vector<int>{2, 3, 5, 1}, 5)) ==
         (vector<int>{ 100000000,
                       203005001,
                       412020034,
                       836060192,
                      1696160752}));
  {
    constexpr int MAX_N = 10;
    constexpr int MAX_M = 15;
    mt19937_64 rng;
    SetMul<Mint, MAX_N - 1> setMul;
    for (int n = 0; n <= MAX_N; ++n) for (int m = 0; m <= MAX_M; ++m) {
      // put garbage
      for (int h = 0; h < 1 << (MAX_N - 1); ++h) for (int k = 0; k <= MAX_N - 1; ++k) setMul.zas[h][k] = static_cast<unsigned long long>(rng());
      for (int h = 0; h < 1 << (MAX_N - 1); ++h) for (int k = 0; k <= MAX_N - 1; ++k) setMul.zbs[h][k] = static_cast<unsigned long long>(rng());
      vector<Mint> as(1 << n), bs(1 << n);
      for (int h = 0; h < 1 << n; ++h) as[h] = static_cast<unsigned long long>(rng());
      for (int h = 0; h < 1 << n; ++h) bs[h] = static_cast<unsigned long long>(rng());
      vector<Mint> expected(m, 0);
      auto cs = as;
      for (int i = 0; i < m; ++i) {
        expected[i] = cs[(1 << n) - 1];
        cs = mulBrute(n, cs, bs);
      }
      assert(setMul.powProjPoly(n, as, bs, m) == expected);
    }
  }
}

int main() {
  unittest_setMul(); cerr << "PASSED unittest_setMul" << endl;
  unittest_setExp(); cerr << "PASSED unittest_setExp" << endl;
  unittest_setCom(); cerr << "PASSED unittest_setCom" << endl;
  unittest_setPowProj(); cerr << "PASSED unittest_setPowProj" << endl;
  unittest_setComPoly(); cerr << "PASSED unittest_setComPoly" << endl;
  unittest_setPowProjPoly(); cerr << "PASSED unittest_setPowProjPoly" << endl;
  return 0;
}
