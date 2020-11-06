#include <vector>

#include "modint.h"

using std::vector;

// det(t I - A), division free, O(n^4)
template <class T> vector<T> charPoly(const vector<vector<T>> &a) {
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
  for (int i = n - 1; i >= 0; i -= 2) {
    ps[i] *= -1;
  }
  return ps;
}


constexpr int MO = 998244353;
using Mint = ModInt<MO>;

void unittest() {
  {
    vector<vector<Mint>> a{{3, 1, 4}, {1, 5, 9}, {2, 6, 5}};
    const auto ps = charPoly(a);
    assert(ps.size() == 3 + 1);
    assert(ps[0].x == 90);
    assert(ps[1].x == MO - 8);
    assert(ps[2].x == MO - 13);
    assert(ps[3].x == 1);
  }
  {
    vector<vector<Mint>> a{{3, 5, 8, 9}, {7, 9, 3, 2}, {3, 8, 4, 6}, {2, 6, 4, 3}};
    const auto ps = charPoly(a);
    assert(ps.size() == 4 + 1);
    assert(ps[0].x == MO - 491);
    assert(ps[1].x == MO - 317);
    assert(ps[2].x == MO - 14);
    assert(ps[3].x == MO - 19);
    assert(ps[4].x == 1);
  }
}

int main() {
  unittest();
  return 0;
}
