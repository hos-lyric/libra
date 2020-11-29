#include <vector>

#include "modint.h"

using std::swap;
using std::vector;

// det(x I + a)
// O(n^3)
template <class T> vector<T> charPoly(const vector<vector<T>> &a) {
  const int n = a.size();
  auto b = a;
  // upper Hessenberg
  for (int j = 0; j < n - 2; ++j) {
    for (int i = j + 1; i < n; ++i) {
      if (b[i][j]) {
        swap(b[j + 1], b[i]);
        for (int ii = 0; ii < n; ++ii) swap(b[ii][j + 1], b[ii][i]);
        break;
      }
    }
    if (b[j + 1][j]) {
      const T r = 1 / b[j + 1][j];
      for (int i = j + 2; i < n; ++i) {
        const T s = r * b[i][j];
        for (int jj = j; jj < n; ++jj) b[i][jj] -= s * b[j + 1][jj];
        for (int ii = 0; ii < n; ++ii) b[ii][j + 1] += s * b[ii][i];
      }
    }
  }
  // fss[i] := det(x I_i + b[0..i][0..i])
  vector<vector<T>> fss(n + 1);
  fss[0] = {1};
  for (int i = 0; i < n; ++i) {
    fss[i + 1].assign(i + 2, 0);
    for (int k = 0; k <= i; ++k) fss[i + 1][k + 1] = fss[i][k];
    for (int k = 0; k <= i; ++k) fss[i + 1][k] += b[i][i] * fss[i][k];
    T prod = 1;
    for (int j = i - 1; j >= 0; --j) {
      prod *= -b[j + 1][j];
      const T s = prod * b[j][i];
      for (int k = 0; k <= j; ++k) fss[i + 1][k] += s * fss[j][k];
    }
  }
  return fss[n];
}

// det(x I + a), division free
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


void unittest() {
  constexpr int MO = 998244353;
  using Mint = ModInt<MO>;
  {
    vector<vector<Mint>> a{
        {3, 1, 4},
        {1, 5, 9},
        {2, 6, 5},
    };
    const auto ps = charPoly(a);
    assert(ps.size() == 3 + 1);
    assert(ps[0].x == MO - 90);
    assert(ps[1].x == MO - 8);
    assert(ps[2].x == 13);
    assert(ps[3].x == 1);
    assert(ps == charPolyDivFree(a));
  }
  {
    vector<vector<Mint>> a{
        {3, -5, 8, 9},
        {-7, 9, -3, 2},
        {3, 8, -4, -6},
        {2, -6, 4, 3},
    };
    const auto ps = charPoly(a);
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
    const auto ps = charPoly(a);
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
}

int main() {
  unittest();
  return 0;
}
