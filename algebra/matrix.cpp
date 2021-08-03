#include <vector>

#include "modint.h"

using std::swap;
using std::vector;

// det(a + x I)
// O(n^3)
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

// det(a + x b)
// O(n^3)
template <class T> vector<T> detPoly(vector<vector<T>> a, vector<vector<T>> b) {
  const int n = a.size();
  T prod = 1;
  int off = 0;
  for (int h = 0; h < n; ++h) {
    for (; ; ) {
      if (b[h][h]) break;
      for (int j = h + 1; j < n; ++j) {
        if (b[h][j]) {
          prod *= -1;
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

////////////////////////////////////////////////////////////////////////////////

void unittest() {
  constexpr unsigned MO = 998244353;
  using Mint = ModInt<MO>;

  // charPoly, charPolyDivFree
  {
    const vector<vector<Mint>> a;
    const vector<Mint> ps = charPoly(a);
    assert(ps.size() == 0 + 1);
    assert(ps[0].x == 1);
    assert(ps == charPolyDivFree(a));
  }
  {
    const vector<vector<Mint>> a{{10}};
    const vector<Mint> ps = charPoly(a);
    assert(ps.size() == 1 + 1);
    assert(ps[0].x == 10);
    assert(ps[1].x == 1);
    assert(ps == charPolyDivFree(a));
  }
  {
    const vector<vector<Mint>> a{
        {3, 1, 4},
        {1, 5, 9},
        {2, 6, 5},
    };
    const vector<Mint> ps = charPoly(a);
    assert(ps.size() == 3 + 1);
    assert(ps[0].x == MO - 90);
    assert(ps[1].x == MO - 8);
    assert(ps[2].x == 13);
    assert(ps[3].x == 1);
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
    assert(ps.size() == 4 + 1);
    assert(ps[0].x == 181);
    assert(ps[1].x == MO - 171);
    assert(ps[2].x == MO - 14);
    assert(ps[3].x == 11);
    assert(ps[4].x == 1);
    assert(ps == charPolyDivFree(a));
  }
  {
    constexpr int n = 100;
    vector<vector<Mint>> a(n, vector<Mint>(n));
    for (int i = 0; i < n; ++i) for (int j = 0; j < n; ++j) {
      a[i][j] = (i * j * j) % 199 - 100;
    }
    const vector<Mint> ps = charPoly(a);
    assert(ps.size() == static_cast<size_t>(n + 1));
    assert(ps[0].x == 0);
    assert(ps[1].x == 895461868);
    assert(ps[2].x == 863013394);
    assert(ps[49].x == 301922511);
    assert(ps[50].x == 222844028);
    assert(ps[51].x == 443314937);
    assert(ps[98].x == 997237804);
    assert(ps[99].x == 998243734);
    assert(ps[100].x == 1);
    assert(ps == charPolyDivFree(a));
  }

  // detPoly
  {
    const vector<vector<Mint>> a;
    const vector<vector<Mint>> b;
    const vector<Mint> ps = detPoly(a, b);
    assert(ps.size() == 0 + 1);
    assert(ps[0].x == 1);
  }
  {
    const vector<vector<Mint>> a{{20}};
    const vector<vector<Mint>> b{{33}};
    const vector<Mint> ps = detPoly(a, b);
    assert(ps.size() == 1 + 1);
    assert(ps[0].x == 20);
    assert(ps[1].x == 33);
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
    assert(ps.size() == 3 + 1);
    assert(ps[0].x == MO - 90);
    assert(ps[1].x == MO - 15);
    assert(ps[2].x == 132);
    assert(ps[3].x == MO - 15);
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
    assert(ps.size() == 3 + 1);
    assert(ps[0].x == MO - 90);
    assert(ps[1].x == MO - 76);
    assert(ps[2].x == 46);
    assert(ps[3].x == 0);
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
    assert(ps.size() == 4 + 1);
    assert(ps[0].x == MO - 6356);
    assert(ps[1].x == 7362);
    assert(ps[2].x == MO - 5875);
    assert(ps[3].x == 646);
    assert(ps[4].x == 0);
  }
}

int main() {
  unittest();
  return 0;
}
