#include <assert.h>
#include <algorithm>
#include <utility>
#include <vector>

using std::min;
using std::pair;
using std::swap;
using std::vector;

// det(a)
// O(n^3)
//   Call by value: Modifies a (Watch out when using C-style array!)
template <class T> T det(vector<vector<T>> a) {
  const int n = a.size();
  T prod = 1;
  for (int h = 0; h < n; ++h) {
    for (int i = h; i < n; ++i) if (a[i][h]) {
      if (h != i) {
        prod = -prod;
        swap(a[h], a[i]);
      }
      break;
    }
    if (!a[h][h]) return 0;
    prod *= a[h][h];
    const T s = a[h][h].inv();
    for (int j = h + 1; j < n; ++j) a[h][j] *= s;
    for (int i = h + 1; i < n; ++i) {
      const T t = a[i][h];
      if (t) for (int j = h + 1; j < n; ++j) a[i][j] -= t * a[h][j];
    }
  }
  return prod;
}

// det(a + x I), division free
// O(n^4)
template <class T> vector<T> charPolyDivFree(const vector<vector<T>> &a) {
  const int n = a.size();
  vector<T> ps(n + 1, 0);
  ps[n] = 1;
  for (int h = n - 1; h >= 0; --h) {
    // closed walks at h with repetition allowed from 0, ..., h - 1
    vector<vector<T>> sub(n, vector<T>(h + 1, 0));
    for (int i = n; i >= 1; --i) {
      sub[i - 1][h] += ps[i];
    }
    for (int i = n - 1; i >= 1; --i) for (int u = 0; u <= h; ++u) {
      for (int v = 0; v < h; ++v) {
        sub[i - 1][v] -= sub[i][u] * a[u][v];
      }
    }
    for (int i = n - 1; i >= 0; --i) for (int u = 0; u <= h; ++u) {
      ps[i] += sub[i][u] * a[u][h];
    }
  }
  return ps;
}

// det(a + x I)
// O(n^3)
//   Call by value: Modifies a (Watch out when using C-style array!)
template <class T> vector<T> charPoly(vector<vector<T>> a) {
  const int n = a.size();
  // upper Hessenberg
  for (int j = 0; j < n - 2; ++j) {
    for (int i = j + 1; i < n; ++i) {
      if (a[i][j]) {
        swap(a[j + 1], a[i]);
        for (int ii = 0; ii < n; ++ii) swap(a[ii][j + 1], a[ii][i]);
        break;
      }
    }
    if (a[j + 1][j]) {
      const T s = 1 / a[j + 1][j];
      for (int i = j + 2; i < n; ++i) {
        const T t = s * a[i][j];
        for (int jj = j; jj < n; ++jj) a[i][jj] -= t * a[j + 1][jj];
        for (int ii = 0; ii < n; ++ii) a[ii][j + 1] += t * a[ii][i];
      }
    }
  }
  // fss[i] := det(a[0..i][0..i] + x I_i)
  vector<vector<T>> fss(n + 1);
  fss[0] = {1};
  for (int i = 0; i < n; ++i) {
    fss[i + 1].assign(i + 2, 0);
    for (int k = 0; k <= i; ++k) fss[i + 1][k + 1] = fss[i][k];
    for (int k = 0; k <= i; ++k) fss[i + 1][k] += a[i][i] * fss[i][k];
    T prod = 1;
    for (int j = i - 1; j >= 0; --j) {
      prod *= -a[j + 1][j];
      const T t = prod * a[j][i];
      for (int k = 0; k <= j; ++k) fss[i + 1][k] += t * fss[j][k];
    }
  }
  return fss[n];
}

// det(a + x b)
// O(n^3)
//   Call by value: Modifies a, b (Watch out when using C-style array!)
template <class T> vector<T> detPoly(vector<vector<T>> a, vector<vector<T>> b) {
  const int n = a.size();
  T prod = 1;
  int off = 0;
  for (int h = 0; h < n; ++h) {
    for (; ; ) {
      if (b[h][h]) break;
      for (int j = h + 1; j < n; ++j) {
        if (b[h][j]) {
          prod = -prod;
          for (int i = 0; i < n; ++i) {
            swap(a[i][h], a[i][j]);
            swap(b[i][h], b[i][j]);
          }
          break;
        }
      }
      if (b[h][h]) break;
      if (++off > n) return vector<T>(n + 1, 0);
      for (int j = 0; j < n; ++j) {
        b[h][j] = a[h][j];
        a[h][j] = 0;
      }
      for (int i = 0; i < h; ++i) {
        const T t = b[h][i];
        for (int j = 0; j < n; ++j) {
          a[h][j] -= t * a[i][j];
          b[h][j] -= t * b[i][j];
        }
      }
    }
    prod *= b[h][h];
    const T s = 1 / b[h][h];
    for (int j = 0; j < n; ++j) {
      a[h][j] *= s;
      b[h][j] *= s;
    }
    for (int i = 0; i < n; ++i) if (h != i) {
      const T t = b[i][h];
      for (int j = 0; j < n; ++j) {
        a[i][j] -= t * a[h][j];
        b[i][j] -= t * b[h][j];
      }
    }
  }
  const vector<T> fs = charPoly(a);
  vector<T> gs(n + 1, 0);
  for (int i = 0; off + i <= n; ++i) gs[i] = prod * fs[off + i];
  return gs;
}

// det(a[0] + x a[1] + ... + x^m a[m])
// O((m n)^3)
//   Call by value: Modifies a (Watch out when using C-style array!)
template <class T> vector<T> detPoly(vector<vector<vector<T>>> a) {
  assert(!a.empty());
  const int m = a.size() - 1, n = a[0].size();
  T prod = 1;
  int off = 0;
  for (int h = 0; h < n; ++h) {
    for (; ; ) {
      if (a[m][h][h]) break;
      for (int j = h + 1; j < n; ++j) {
        if (a[m][h][j]) {
          prod = -prod;
          for (int d = 0; d <= m; ++d) for (int i = 0; i < n; ++i) {
            swap(a[d][i][h], a[d][i][j]);
          }
          break;
        }
      }
      if (a[m][h][h]) break;
      if (++off > m * n) return vector<T>(m * n + 1, 0);
      for (int d = m; --d >= 0; ) for (int j = 0; j < n; ++j) {
        a[d + 1][h][j] = a[d][h][j];
      }
      for (int j = 0; j < n; ++j) {
        a[0][h][j] = 0;
      }
      for (int i = 0; i < h; ++i) {
        const T t = a[m][h][i];
        for (int d = 0; d <= m; ++d) for (int j = 0; j < n; ++j) {
          a[d][h][j] -= t * a[d][i][j];
        }
      }
    }
    prod *= a[m][h][h];
    const T s = 1 / a[m][h][h];
    for (int d = 0; d <= m; ++d) for (int j = 0; j < n; ++j) {
      a[d][h][j] *= s;
    }
    for (int i = 0; i < n; ++i) if (h != i) {
      const T t = a[m][i][h];
      for (int d = 0; d <= m; ++d) for (int j = 0; j < n; ++j) {
        a[d][i][j] -= t * a[d][h][j];
      }
    }
  }
  vector<vector<T>> b(m * n, vector<T>(m * n, 0));
  for (int i = 0; i < (m - 1) * n; ++i) b[i][n + i] = -1;
  for (int d = 0; d < m; ++d) {
    for (int i = 0; i < n; ++i) for (int j = 0; j < n; ++j) {
      b[(m - 1) * n + i][d * n + j] = a[d][i][j];
    }
  }
  const vector<T> fs = charPoly(b);
  vector<T> gs(m * n + 1, 0);
  for (int i = 0; off + i <= m * n; ++i) gs[i] = prod * fs[off + i];
  return gs;
}

// a \in Mat(m, n), rank(a) = r
// b \in Mat(m, r), c \in Mat(r, n), a = b c
// O(m n min(m, n))
//   Call by value: Modifies a (Watch out when using C-style array!)
template <class T>
pair<vector<vector<T>>, vector<vector<T>>> rankDecompose(vector<vector<T>> a) {
  assert(!a.empty());
  const int m = a.size(), n = a[0].size();
  vector<int> is(m);
  for (int i = 0; i < m; ++i) is[i] = i;
  vector<vector<T>> b(m, vector<T>(min(m, n), 0));
  int r = 0;
  for (int h = 0; r < m && h < n; ++h) {
    for (int i = r; i < m; ++i) if (a[i][h]) {
      swap(a[r], a[i]);
      swap(is[r], is[i]);
      break;
    }
    if (a[r][h]) {
      const T s = a[r][h].inv();
      for (int i = r + 1; i < m; ++i) {
        const T t = b[is[i]][r] = s * a[i][h];
        for (int j = h; j < n; ++j) a[i][j] -= t * a[r][j];
      }
      ++r;
    }
  }
  for (int i = 0; i < m; ++i) b[i].resize(r);
  for (int k = 0; k < r; ++k) b[is[k]][k] = 1;
  a.resize(r);
  return std::make_pair(b, a);
}
////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include "modint.h"

using std::cerr;
using std::endl;

// det, charPolyDivFree, charPoly
template <unsigned MO> void unittest_charPoly() {
  using Mint = ModInt<MO>;
  {
    const vector<vector<Mint>> a;
    const vector<Mint> ps = charPoly(a);
    assert(ps == (vector<Mint>{1}));
    assert(ps[0] == det(a));
    assert(ps == charPolyDivFree(a));
  }
  {
    const vector<vector<Mint>> a{{10}};
    const vector<Mint> ps = charPoly(a);
    assert(ps == (vector<Mint>{10, 1}));
    assert(ps[0] == det(a));
    assert(ps == charPolyDivFree(a));
  }
  {
    const vector<vector<Mint>> a{
      {3, 1, 4},
      {1, 5, 9},
      {2, 6, 5},
    };
    const vector<Mint> ps = charPoly(a);
    assert(ps == (vector<Mint>{-90, -8, 13, 1}));
    assert(ps[0] == det(a));
    assert(ps == charPolyDivFree(a));
  }
  {
    const vector<vector<Mint>> a{
      {3, -5, 8, 9},
      {-7, 9, -3, 2},
      {3, 8, -4, -6},
      {2, -6, 4, 3},
    };
    const vector<Mint> ps = charPoly(a);
    assert(ps == (vector<Mint>{181, -171, -14, 11, 1}));
    assert(ps[0] == det(a));
    assert(ps == charPolyDivFree(a));
  }
}

// detPoly
template <unsigned MO> void unittest_detPoly() {
  using Mint = ModInt<MO>;
  {
    const vector<vector<Mint>> a;
    const vector<vector<Mint>> b;
    const vector<Mint> ps = detPoly(a, b);
    assert(ps == (vector<Mint>{1}));
    assert(ps == detPoly(vector<vector<vector<Mint>>>{a, b}));
  }
  {
    const vector<vector<Mint>> a{{20}};
    const vector<vector<Mint>> b{{33}};
    const vector<Mint> ps = detPoly(a, b);
    assert(ps == (vector<Mint>{20, 33}));
    assert(ps == detPoly(vector<vector<vector<Mint>>>{a, b}));
  }
  {
    const vector<vector<Mint>> a{
      {3, 1, 4},
      {1, 5, 9},
      {2, 6, 5},
    };
    const vector<vector<Mint>> b{
      {3, 5, 8},
      {9, 7, 9},
      {3, 2, 3},
    };
    const vector<Mint> ps = detPoly(a, b);
    assert(ps == (vector<Mint>{-90, -15, 132, -15}));
    assert(ps == detPoly(vector<vector<vector<Mint>>>{a, b}));
  }
  {
    const vector<vector<Mint>> a{
      {3, 1, 4},
      {1, 5, 9},
      {2, 6, 5},
    };
    const vector<vector<Mint>> b{
      {3, 5, 8},
      {9, 7, 9},
      {6, 2, 1},
    };
    const vector<Mint> ps = detPoly(a, b);
    assert(ps == (vector<Mint>{-90, -76, 46, 0}));
    assert(ps == detPoly(vector<vector<vector<Mint>>>{a, b}));
  }
  {
    const vector<vector<Mint>> a{
      {1, 2, 3, -5},
      {8, -3, 1, -4},
      {5, 9, -4, -3},
      {-7, 0, -7, -7},
    };
    const vector<vector<Mint>> b{
      {0, 0, 1, 2},
      {0, 0, 3, 4},
      {5, 6, 7, 8},
      {10, 12, 4, 6},
    };
    const vector<Mint> ps = detPoly(a, b);
    assert(ps == (vector<Mint>{-6356, 7362, -5875, 646, 0}));
    assert(ps == detPoly(vector<vector<vector<Mint>>>{a, b}));
  }
  {
    const vector<vector<vector<Mint>>> a{
      {
        {2, 0, 3},
        {0, 4, 8},
        {1, 5, 4},
      }, {
        {-1, -2, -9},
        {-7, 3, 4},
        {8, 6, -5},
      }, {
        {2, 4, 7},
        {8, 6, 8},
        {5, 1, 0},
      }
    };
    const vector<Mint> ps = detPoly(a);
    assert(ps == (vector<Mint>{-60, -318, 188, 17, -488, 304, -10}));
  }
  {
    const vector<vector<vector<Mint>>> a{
      {
        {2, 0, 3},
        {0, 4, 8},
        {1, 5, 4},
      }, {
        {-1, -2, -9},
        {-7, 3, 4},
        {8, -1, 5},
      }, {
        {12, 8, 12},
        {8, 6, 8},
        {-16, -12, -16},
      }
    };
    const vector<Mint> ps = detPoly(a);
    assert(ps == (vector<Mint>{-60, -126, 459, -122, 294, 152, 0}));
  }
  {
    const vector<vector<vector<Mint>>> a{
      {
        {0, 0, 0, 0},
        {0, 0, 0, 0},
        {0, 0, 0, 0},
        {0, 0, 0, 0},
      }, {
        {0, 1, 0, 0},
        {0, 0, 1, 0},
        {0, 1, 0, 0},
        {0, 0, 0, 1},
      }, {
        {0, 0, 0, 1},
        {0, 1, 1, 0},
        {0, 0, 0, 0},
        {0, 1, 0, 0},
      }, {
        {1, 0, 0, 0},
        {0, 1, 1, 0},
        {1, 1, 0, 0},
        {0, 0, 0, 1},
      }, {
        {0, 0, 0, 1},
        {0, 0, 1, 0},
        {0, 1, 0, 1},
        {0, 1, 1, 0},
      }, {
        {0, 0, 0, 0},
        {0, 0, 0, 0},
        {0, 0, 0, 0},
        {0, 0, 0, 0},
      }
    };
    const vector<Mint> ps = detPoly(a);
    assert(ps == (vector<Mint>{0, 0, 0, 0, 0, 0, 0, 0, -2, -3, -5, -5, -3, -3, -1, 0, 0, 0, 0, 0, 0}));
  }
}

// rankDecompose
template <unsigned MO> void unittest_rankDecompose() {
  using Mint = ModInt<MO>;
  auto test_rankDecompose = [&](const vector<vector<Mint>> &a, int r) -> void {
    const int m = a.size(), n = a[0].size();
    const auto res = rankDecompose(a);
    const vector<vector<Mint>> &b = res.first, &c = res.second;
    assert(b.size() == static_cast<size_t>(m));
    for (int i = 0; i < m; ++i) assert(b[i].size() == static_cast<size_t>(r));
    assert(c.size() == static_cast<size_t>(r));
    for (int k = 0; k < r; ++k) assert(c[k].size() == static_cast<size_t>(n));
    vector<vector<Mint>> prod(m, vector<Mint>(n, 0));
    for (int i = 0; i < m; ++i) for (int k = 0; k < r; ++k) for (int j = 0; j < n; ++j) {
      prod[i][j] += b[i][k] * c[k][j];
    }
    assert(a == prod);
  };
  {
    test_rankDecompose({{0}}, 0);
    test_rankDecompose({{1}}, 1);
    test_rankDecompose({{2}}, (MO == 2) ? 0 : 1);
    test_rankDecompose({
      {0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0},
      {0, 0, 0, 0, 0},
    }, 0);
    test_rankDecompose({
      {0, 0, 0, 0, 0},
      {0, 0, 4, 6, 8},
      {0, 0, 6, 9, 12},
    }, 1);
    test_rankDecompose({
      {9, 8, 7, 6, 5},
      {9, 8, 7, 6, 5},
      {7, 5, 3, 2, 1},
    }, 2);
    test_rankDecompose({
      {1, 2, 1, 3, 1},
      {2, 1, 4, 1, 2},
      {1, 3, 1, 2, 1},
    }, (MO == 2) ? 2 : 3);
    test_rankDecompose({
      {0, 0, 0},
      {0, 0, 0},
      {0, 0, 0},
      {0, 0, 0},
      {0, 0, 0},
    }, 0);
    test_rankDecompose({
      {1, 3, 9},
      {2, 6, 18},
      {4, 12, 36},
      {8, 24, 72},
      {16, 48, 144},
    }, 1);
    test_rankDecompose({
      {6, 11, 10},
      {3, 4, 5},
      {3, 5, 5},
      {3, 6, 5},
      {0, 1, 0},
    }, 2);
    test_rankDecompose({
      {0, 1, 0},
      {1, 0, 0},
      {0, 0, 1},
      {0, 1, 0},
      {0, 0, 1},
    }, 3);
  }
}

template <unsigned MO> void unittests() {
  unittest_charPoly<MO>(); cerr << "PASSED unittest_charPoly<" << MO << ">" << endl;
  unittest_detPoly<MO>(); cerr << "PASSED unittest_detPoly<" << MO << ">" << endl;
  unittest_rankDecompose<MO>(); cerr << "PASSED unittest_rankDecompose<" << MO << ">" << endl;
}

int main() {
  unittests<998244353>();
  unittests<2>();
  unittests<3>();
  return 0;
}
