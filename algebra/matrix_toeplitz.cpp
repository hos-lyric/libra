#include <assert.h>
#include <vector>

using std::vector;

// TODO: refactor det, mod_monic::power

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

// fs represents f(X) = X^|fs| - \sum[0<=i<|fs|] fs[i] X^i
namespace mod_monic {
// X^e mod f(X)
template <class T> vector<T> power(long long e, const vector<T> &fs) {
  assert(e >= 0);
  const int deg = fs.size();
  if (e == 0) {
    vector<T> gs(deg, 0);
    if (deg) gs[0] = 1;
    return gs;
  } else {
    const auto gs = power(e >> 1, fs);
    vector<T> hs(2 * deg - 1);
    for (int i = 0; i < deg; ++i) for (int j = 0; j < deg; ++j) hs[i + j] += gs[i] * gs[j];
    for (int i = deg - 1; --i >= 0; ) for (int j = 0; j < deg; ++j) hs[i + j] += fs[j] * hs[i + deg];
    if (e & 1) {
      hs.insert(hs.begin(), 0);
      for (int j = 0; j < deg; ++j) hs[j] += fs[j] * hs[deg];
    }
    hs.resize(deg);
    return hs;
  }
}
}  // namespace mod_monic

// det(as[off + j-i])_{0<=i,j<n}
//   l <= j-i <= r
//   O(min{-l, r}^3 + (r-l) log(r-l) log(n)) time (can use FFT for huge n)
template <class T> T detToeplitz(const T *as, int l, int r, long long n) {
  assert(n >= 0);
  if (n == 0) return 1;
  if (l < -(n - 1)) l = -(n - 1);
  if (r > +(n - 1)) r = +(n - 1);
  for (; l <= r && !as[l]; ++l) {}
  for (; l <= r && !as[r]; --r) {}
  if (!(l <= 0 && 0 <= r)) return 0;
  if (l == 0 || 0 == r) return as[0].pow(n);
  T leading;
  vector<T> fs(r - l);
  if (-l <= r) {
    // sweep by rows [-l, n) <-> mod f(X)
    // rows [0, -l): -X^(n+r-l, n+r] mod f(X)
    leading = as[l];
    const T invLeading = as[l].inv();
    for (int i = 0; i < r - l; ++i) fs[i] = -invLeading * as[r - i];
    const int ll = -r, rr = -l;
    l = ll;
    r = rr;
  } else {
    // sweep by columns [r, n) <-> mod f(X)
    // columns [0, r): -X^(n-l+r, n-l] mod f(X)
    leading = as[r];
    const T invLeading = as[r].inv();
    for (int i = 0; i < r - l; ++i) fs[i] = -invLeading * as[l + i];
  }
  vector<vector<T>> b(r, vector<T>(r));
  vector<T> gs = mod_monic::power(n - l, fs);
  for (int i = r; --i >= 0; ) {
    for (int j = 0; j < r; ++j) b[i][j] = gs[r - l - 1 - j];
    gs.insert(gs.begin(), 0);
    for (int j = 1; j < r - l; ++j) gs[j] += fs[j] * gs[r - l];
    gs.pop_back();
  }
  return ((r & n & 1) ? -1 : +1) * leading.pow(n) * det(b);
}

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <random>
#include "modint.h"

using std::cerr;
using std::endl;
using std::mt19937_64;

template <unsigned MO> void unittest() {
  using Mint = ModInt<MO>;
  {
    const Mint as[] = {5, 1, 2, 7};
    assert(detToeplitz(as + 1, -1, 2, 6) == 20376);
    assert(detToeplitz(as + 2, -2, 1, 6) == 47622);
    assert(detToeplitz(as, 100, 0, 6) == 0);
    assert(detToeplitz(as, 0, -100, 6) == 0);
    assert(detToeplitz(as, 100, -100, 0) == 1);
  }
  {
    constexpr int LIM = 10;
    mt19937_64 rng;
    for (int l = 0; l >= -LIM; --l) for (int r = 0; r - l <= LIM; ++r) {
      for (int p = 0; p < 1 << (r - l + 1); ++p) {
        for (int n = 0; n <= LIM; ++n) {
          vector<Mint> as_(r - l + 1, 0);
          Mint *as = as_.data() - l;
          for (int i = l; i <= r; ++i) if (p >> (i - l) & 1) {
            as[i] = 1 + static_cast<unsigned long long>(rng()) % (MO - 1);
          }
          vector<vector<Mint>> a(n, vector<Mint>(n, 0));
          for (int i = 0; i < n; ++i) for (int j = 0; j < n; ++j) {
            if (l <= j - i && j - i <= r) a[i][j] = as[j - i];
          }
          assert(detToeplitz(as, l, r, n) == det(a));
        }
      }
    }
  }
}

template <unsigned MO> void unittests() {
  unittest<MO>(); cerr << "PASSED unittest<" << MO << ">" << endl;
}

int main() {
  unittests<998244353>();
  unittests<2>();
  unittests<3>();
  return 0;
}
