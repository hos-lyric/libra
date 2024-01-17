#include <assert.h>
#include <string.h>
#include <vector>

using std::vector;

// as * bs
// ZT: T[2^n][n+1]
template <class T, class ZT>
vector<T> setMul(int n, const vector<T> &as, const vector<T> &bs, ZT zas, ZT zbs) {
  assert(static_cast<int>(as.size()) == 1 << n);
  assert(static_cast<int>(bs.size()) == 1 << n);
  // ranked
  for (int h = 0; h < 1 << n; ++h) {
    memset(zas[h], 0, (n + 1) * sizeof(T));
    zas[h][__builtin_popcount(h)] = as[h];
  }
  for (int h = 0; h < 1 << n; ++h) {
    memset(zbs[h], 0, (n + 1) * sizeof(T));
    zbs[h][__builtin_popcount(h)] = bs[h];
  }
  // zeta
  for (int w = 1; w < 1 << n; w <<= 1) {
    for (int h0 = 0; h0 < 1 << n; h0 += w << 1) for (int h = h0; h < h0 + w; ++h) {
      for (int k = 0; k <= n; ++k) zas[h + w][k] += zas[h][k];
    }
  }
  for (int w = 1; w < 1 << n; w <<= 1) {
    for (int h0 = 0; h0 < 1 << n; h0 += w << 1) for (int h = h0; h < h0 + w; ++h) {
      for (int k = 0; k <= n; ++k) zbs[h + w][k] += zbs[h][k];
    }
  }
  // product
  for (int h = 0; h < 1 << n; ++h) {
    for (int k = n; k >= 0; --k) {
      T t = 0;
      for (int l = 0; l <= k; ++l) t += zas[h][l] * zbs[h][k - l];
      zas[h][k] = t;
    }
  }
  // moebius
  for (int w = 1; w < 1 << n; w <<= 1) {
    for (int h0 = 0; h0 < 1 << n; h0 += w << 1) for (int h = h0; h < h0 + w; ++h) {
      for (int k = 0; k <= n; ++k) zas[h + w][k] -= zas[h][k];
    }
  }
  // unrank
  vector<T> cs(1 << n);
  for (int h = 0; h < 1 << n; ++h) cs[h] = zas[h][__builtin_popcount(h)];
  return cs;
}

// exp(as)
//   assume as[0] == 0
//   exp(a0 + a1 X) = exp(a0) + exp(a0) a1 X
// ZT1: T[2^(n-1)][n]
// ZT: T[2^n][n+1]
template <class T, class ZT1, class ZT>
vector<T> setExp(int n, const vector<T> &as, ZT1 zas, ZT zbs) {
  assert(static_cast<int>(as.size()) == 1 << n);
  assert(as[0] == 0);
  zbs[0][0] = 1;
  for (int m = 0; m < n; ++m) {
    // ranked a[2^m, 2^(m+1))
    for (int h = 0; h < 1 << m; ++h) {
      memset(zas[h], 0, (m + 1) * sizeof(T));
      zas[h][__builtin_popcount(h)] = as[(1 << m) + h];
    }
    // zeta
    for (int w = 1; w < 1 << m; w <<= 1) {
      for (int h0 = 0; h0 < 1 << m; h0 += w << 1) for (int h = h0; h < h0 + w; ++h) {
        for (int k = 0; k <= m; ++k) zas[h + w][k] += zas[h][k];
      }
    }
    for (int h = 0; h < 1 << m; ++h) {
      // zeta
      zbs[h][m + 1] = 0;
      memcpy(zbs[(1 << m) + h], zbs[h], ((m + 1) + 1) * sizeof(T));
      // product
      for (int k = 0; k <= m; ++k) for (int l = 0; l <= m - k; ++l) {
        zbs[(1 << m) + h][k + l + 1] += zbs[h][k] * zas[h][l];
      }
    }
  }
  // moebius
  for (int w = 1; w < 1 << n; w <<= 1) {
    for (int h0 = 0; h0 < 1 << n; h0 += w << 1) for (int h = h0; h < h0 + w; ++h) {
      for (int k = 0; k <= n; ++k) zbs[h + w][k] -= zbs[h][k];
    }
  }
  // unrank
  vector<T> bs(1 << n);
  for (int h = 0; h < 1 << n; ++h) bs[h] = zbs[h][__builtin_popcount(h)];
  return bs;
}

// \sum[0<=i<=n] fs[i] as^i/i!
//   assume as[0] == 0
//   f(a0 + a1 X) + f(a0) + f'(a0) a1 X
// ZT1: T[2^(n-1)][n]
// ZT: T[2^(n+1)][n+1]
template <class T, class ZT1, class ZT>
vector<T> setCom(int n, const vector<T> &fs, const vector<T> &as, ZT1 zas, ZT zbs) {
  assert(static_cast<int>(fs.size()) == n + 1);
  assert(static_cast<int>(as.size()) == 1 << n);
  assert(as[0] == 0);
  // zbs[2^(n-i), 2^(n-i+1)): composite f^(i)
  for (int i = 0; i <= n; ++i) zbs[1<<(n-i)][0] = fs[i];
  for (int m = 0; m < n; ++m) {
    // ranked a[2^m, 2^(m+1))
    for (int h = 0; h < 1 << m; ++h) {
      memset(zas[h], 0, (m + 1) * sizeof(T));
      zas[h][__builtin_popcount(h)] = as[(1 << m) + h];
    }
    // zeta
    for (int w = 1; w < 1 << m; w <<= 1) {
      for (int h0 = 0; h0 < 1 << m; h0 += w << 1) for (int h = h0; h < h0 + w; ++h) {
        for (int k = 0; k <= m; ++k) zas[h + w][k] += zas[h][k];
      }
    }
    for (int i = 0; i < n - m; ++i) {
      for (int h = 0; h < 1 << m; ++h) {
        // zeta
        zbs[(1<<(n-i)) + h][m + 1] = 0;
        memcpy(zbs[(1<<(n-i)) + (1 << m) + h], zbs[(1<<(n-i)) + h], ((m + 1) + 1) * sizeof(T));
        // product
        for (int k = 0; k <= m; ++k) for (int l = 0; l <= m - k; ++l) {
          zbs[(1<<(n-i)) + (1 << m) + h][k + l + 1] += zbs[(1<<(n-(i+1))) + h][k] * zas[h][l];
        }
      }
    }
  }
  // moebius
  for (int w = 1; w < 1 << n; w <<= 1) {
    for (int h0 = 0; h0 < 1 << n; h0 += w << 1) for (int h = h0; h < h0 + w; ++h) {
      for (int k = 0; k <= n; ++k) zbs[(1<<n) + h + w][k] -= zbs[(1<<n) + h][k];
    }
  }
  // unrank
  vector<T> bs(1 << n);
  for (int h = 0; h < 1 << n; ++h) bs[h] = zbs[(1<<n) + h][__builtin_popcount(h)];
  return bs;
}

// \sum[i] fs[i] as^i
//   not necessarily as[0] == 0
// ZT1: T[2^(n-1)][n]
// ZT: T[2^(n+1)][n+1]
template <class T, class ZT1, class ZT>
vector<T> setComPoly(int n, vector<T> fs, vector<T> as, ZT1 zas, ZT zbs) {
  assert(static_cast<int>(as.size()) == 1 << n);
  const int fsLen = fs.size();
  if (fsLen == 0) return vector<T>(1 << n, 0);
  vector<T> gs(n + 1);
  for (int i = 0; i <= n; ++i) {
    T t = 0;
    for (int j = fsLen; --j >= 0; ) (t *= as[0]) += fs[j];
    gs[i] = t;
    for (int j = 1; j < fsLen; ++j) fs[j - 1] = j * fs[j];
    fs[fsLen - 1] = 0;
  }
  as[0] = 0;
  return setCom(n, gs, as, zas, zbs);
}

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
    int zas[1 << 3][3 + 1];
    int zbs[1 << 3][3 + 1];
    assert(setMul(3,
                  vector<int>{1, 2, 3, 4, 5, 6, 7, 8},
                  vector<int>{9, 10, 11, 12, 13, 14, 15, 16},
                  zas, zbs) ==
           (vector<int>{9, 28, 38, 100, 58, 144, 172, 408}));
  }
  {
    constexpr int MAX_N = 10;
    static Mint zas[1 << MAX_N][MAX_N + 1];
    static Mint zbs[1 << MAX_N][MAX_N + 1];
    for (int n = 0; n <= MAX_N; ++n) {
      // garbage
      for (int h = 0; h < 1 << MAX_N; ++h) for (int k = 0; k <= MAX_N; ++k) zas[h][k] = xrand();
      for (int h = 0; h < 1 << MAX_N; ++h) for (int k = 0; k <= MAX_N; ++k) zbs[h][k] = xrand();
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
      assert(setMul(n, as, bs, zas, zbs) == expected);
    }
  }
}

void unittest_setExp() {
  {
    int zas[1 << 2][2 + 1];
    int zbs[1 << 3][3 + 1];
    assert(setExp(3, vector<int>{0, 2, 3, 5, 7, 11, 13, 17}, zas, zbs) ==
           (vector<int>{1, 2, 3, 11, 7, 25, 34, 153}));
  }
  {
    constexpr int MAX_N = 10;
    static Mint zas[1 << MAX_N][MAX_N + 1];
    static Mint zbs[1 << MAX_N][MAX_N + 1];
    for (int n = 0; n <= MAX_N; ++n) {
      // garbage
      for (int h = 0; h < 1 << MAX_N; ++h) for (int k = 0; k <= MAX_N; ++k) zas[h][k] = xrand();
      for (int h = 0; h < 1 << MAX_N; ++h) for (int k = 0; k <= MAX_N; ++k) zbs[h][k] = xrand();
      //
      vector<Mint> as(1 << n);
      for (int h = 0; h < 1 << n; ++h) as[h] = xrand();
      as[0] = 0;
      vector<Mint> expected(1 << n, 0);
      {
        vector<Mint> prod(1 << n, 0);
        prod[0] = 1;
        for (int i = 0; i <= n; ++i) {
          for (int h = 0; h < 1 << n; ++h) expected[h] += prod[h];
          prod = setMul(n, prod, as, zas, zbs);
          for (int h = 0; h < 1 << n; ++h) prod[h] /= (i + 1);
        }
        for (int h = 0; h < 1 << n; ++h) assert(prod[h] == 0);
      }
      assert(setExp(n, as, zas, zbs) == expected);
    }
  }
}

void unittest_setCom() {
  {
    int zas[1 << 2][2 + 1];
    int zbs[1 << 4][3 + 1];
    assert(setCom(3,
                  vector<int>{10, 1000, 100000, 10000000},
                  vector<int>{0, 2, 3, 5, 7, 11, 13, 17},
                  zas, zbs) ==
           (vector<int>{       10,
                             2000,
                             3000,
                           605000,
                             7000,
                          1411000,
                          2113000,
                        429417000}));
  }
  {
    constexpr int MAX_N = 10;
    static Mint zas[1 << MAX_N][MAX_N + 1];
    static Mint zbs[1 << (MAX_N + 1)][MAX_N + 1];
    for (int n = 0; n <= MAX_N; ++n) {
      // garbage
      for (int h = 0; h < 1 << MAX_N; ++h) for (int k = 0; k <= MAX_N; ++k) zas[h][k] = xrand();
      for (int h = 0; h < 1 << (MAX_N + 1); ++h) for (int k = 0; k <= MAX_N; ++k) zbs[h][k] = xrand();
      //
      vector<Mint> fs(n + 1), as(1 << n);
      for (int i = 0; i <= n; ++i) fs[i] = xrand();
      for (int h = 0; h < 1 << n; ++h) as[h] = xrand();
      as[0] = 0;
      vector<Mint> expected(1 << n, 0);
      {
        vector<Mint> prod(1 << n, 0);
        prod[0] = 1;
        for (int i = 0; i <= n; ++i) {
          for (int h = 0; h < 1 << n; ++h) expected[h] += fs[i] * prod[h];
          prod = setMul(n, prod, as, zas, zbs);
          for (int h = 0; h < 1 << n; ++h) prod[h] /= (i + 1);
        }
        for (int h = 0; h < 1 << n; ++h) assert(prod[h] == 0);
      }
      assert(setCom(n, fs, as, zas, zbs) == expected);
    }
  }
}

void unittest_setComPoly() {
  {
    constexpr int MAX_N = 10;
    static Mint zas[1 << MAX_N][MAX_N + 1];
    static Mint zbs[1 << (MAX_N + 1)][MAX_N + 1];
    for (int n = 0; n <= MAX_N; ++n) for (int m = 0; m <= 2 * n; ++m) {
      // garbage
      for (int h = 0; h < 1 << MAX_N; ++h) for (int k = 0; k <= MAX_N; ++k) zas[h][k] = xrand();
      for (int h = 0; h < 1 << (MAX_N + 1); ++h) for (int k = 0; k <= MAX_N; ++k) zbs[h][k] = xrand();
      //
      vector<Mint> fs(m), as(1 << n);
      for (int i = 0; i < m; ++i) fs[i] = xrand();
      for (int h = 0; h < 1 << n; ++h) as[h] = xrand();
      vector<Mint> expected(1 << n, 0);
      {
        vector<Mint> prod(1 << n, 0);
        prod[0] = 1;
        for (int i = 0; i < m; ++i) {
          for (int h = 0; h < 1 << n; ++h) expected[h] += fs[i] * prod[h];
          prod = setMul(n, prod, as, zas, zbs);
        }
      }
      assert(setComPoly(n, fs, as, zas, zbs) == expected);
    }
  }
}

int main() {
  unittest_setMul(); cerr << "PASSED unittest_setMul" << endl;
  unittest_setExp(); cerr << "PASSED unittest_setExp" << endl;
  unittest_setCom(); cerr << "PASSED unittest_setCom" << endl;
  unittest_setComPoly(); cerr << "PASSED unittest_setComPoly" << endl;
  return 0;
}
