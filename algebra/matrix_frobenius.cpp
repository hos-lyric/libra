#include <assert.h>
#include <algorithm>
#include <chrono>
#include <random>
#include <vector>

using std::vector;

#ifdef LOCAL
std::mt19937_64 rng(58);
#else
std::mt19937_64 rng(std::chrono::steady_clock::now().time_since_epoch().count());
#endif

namespace square_matrix {
template <class T> vector<vector<T>> transpose(const vector<vector<T>> &a) {
  const int n = a.size();
  for (int i = 0; i < n; ++i) assert(static_cast<int>(a[i].size()) == n);
  vector<vector<T>> b(n, vector<T>(n));
  for (int i = 0; i < n; ++i) for (int j = 0; j < n; ++j) b[j][i] = a[i][j];
  return b;
}
template <class T> vector<T> mul(const vector<vector<T>> &a, const vector<T> &us) {
  const int n = a.size();
  assert(static_cast<int>(us.size()) == n);
  vector<T> vs(n, 0);
  for (int i = 0; i < n; ++i) {
    assert(static_cast<int>(a[i].size()) == n);
    for (int j = 0; j < n; ++j) vs[i] += a[i][j] * us[j];
  }
  return vs;
}
template <class T> vector<vector<T>> mul(const vector<vector<T>> &a, const vector<vector<T>> &b) {
  const int n = a.size();
  for (int i = 0; i < n; ++i) assert(static_cast<int>(a[i].size()) == n);
  assert(static_cast<int>(b.size()) == n);
  for (int j = 0; j < n; ++j) assert(static_cast<int>(b[j].size()) == n);
  const auto bT = transpose(b);
  vector<vector<T>> c(n, vector<T>(n, 0));
  for (int i = 0; i < n; ++i) for (int j = 0; j < n; ++j) for (int k = 0; k < n; ++k) {
    c[i][j] += a[i][k] * bT[j][k];
  }
  return c;
}
}  // namespace square_matrix

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

// a: coefficients to represent c by b
// b: basis consisting of added row vectors
// c: reduced basis
// invariants:
//   a b = c
//   c[i] = 0 or c[i][i] = 1
//   c: upper triangular
template <class T> struct Basis {
  int n;
  vector<vector<T>> a, b, c;
  Basis() {}
  Basis(int n_) : n(n_), a(n, vector<T>(n, 0)), c(n, vector<T>(n, 0)) {}
  inline int size() const {
    return b.size();
  }
  // Returns true iff us extends the span.
  // ps: coefficients to represent us by b
  vector<T> ps;
  bool add(const vector<T> &us) {
    // invariant: us = vs + \sum[k] ps[k] b[k]
    auto vs = us;
    for (int k = 0; k < size(); ++k) ps[k] = 0;
    for (int i = 0; i < n; ++i) if (vs[i]) {
      if (c[i][i]) {
        const T t = vs[i];
        for (int k = 0; k < size(); ++k) ps[k] += t * a[i][k];
        for (int j = i; j < n; ++j) vs[j] -= t * c[i][j];
      } else {
        const T s = vs[i].inv();
        for (int k = 0; k < size(); ++k) a[i][k] = -s * ps[k];
        a[i][size()] = s;
        for (int j = i; j < n; ++j) c[i][j] = s * vs[j];
        for (int k = 0; k < size(); ++k) ps[k] = 0;
        ps.push_back(1);
        b.push_back(us);
        return true;
      }
    }
    return false;
  }
  // (a, c) <- (b^-1, I)
  void reduce() {
    assert(size() == n);
    for (int i = n; --i >= 0; ) for (int j = i + 1; j < n; ++j) {
      for (int k = 0; k < n; ++k) a[i][k] -= c[i][j] * a[j][k];
      c[i][j] = 0;
    }
  }
};

// Frobenius normal form
//       [         pss[0][0]                                ]     
//       [ 1       pss[0][1]                                ]     
//       [   ...   ...                                      ]     
//       [       1 pss[0][$-1]                              ]     
// a = q [                      ...                         ] q^-1
//       [                                  pss[len-1][0]   ]     
//       [                          1       pss[len-1][1]   ]     
//       [                            ...   ...             ]     
//       [                                1 pss[len-1][$-1] ]     
//        |                    |   |                       |      
//      pt[0]               pt[1] pt[len-1]             pt[len]   
// p[i](X) := T^|pss[i]| - \sum[k] pss[i][k] X^k
//   p[i](X): min poly of K^n / <basis.b[0, pt[i])>
//   p[len-1](X) | ... | p[0](X)
// q, q^-1: transpose of basis.b, basis.a
// Requires T(unsigned long long) to generate a random T.
// Needs the linear map mul(a, *) only.
// https://codeforces.com/blog/entry/124815
template <class T> struct Frobenius {
  int n;
  Basis<T> basis;
  int len;
  vector<int> pt;
  vector<vector<T>> pss;
  Frobenius() {}
  // each try: O(n^3) time, Pr[failure] <= n / (field size), Pr[failure] < 1
  explicit Frobenius(const vector<vector<T>> &a) {
    n = a.size();
    for (int i = 0; i < n; ++i) assert(static_cast<int>(a[i].size()) == n);
   loop:
    basis = Basis<T>(n);
    len = 0;
    pt = {0};
    pss = {};
    for (; basis.size() < n; ) {
      vector<T> us(n);
      for (int h = 0; h < n; ++h) us[h] = static_cast<unsigned long long>(rng());
      auto tester = basis;
      for (auto vs = us; tester.add(vs); vs = square_matrix::mul(a, vs)) {}
      const int di = tester.size() - pt[len];
      pss.emplace_back(tester.ps.end() - di, tester.ps.end());
      for (int j = 0; j < len; ++j) {
        const int dj = pt[j + 1] - pt[j];
        if (dj < di) goto loop;
        // destroys tester.ps[pt[j], pt[j + 1])
        auto rs = tester.ps.begin() + pt[j];
        for (int l = dj - di; --l >= 0; ) for (int k = 0; k < di; ++k) {
          rs[l + k] += pss[len][k] * rs[l + di];
        }
        for (int k = 0; k < di; ++k) if (rs[k]) goto loop;
        for (int l = 0; l < dj - di; ++l) for (int h = 0; h < n; ++h) {
          us[h] -= rs[l + di] * basis.b[pt[j] + l][h];
        }
      }
      for (int k = 0; k < di; ++k) {
        basis.add(us);
        us = square_matrix::mul(a, us);
      }
      ++len;
      pt.push_back(basis.size());
    }
    basis.reduce();
  }
  // O(n^2)
  vector<vector<T>> left() const {
    return square_matrix::transpose(basis.b);
  }
  // O(n^2)
  vector<vector<T>> right() const {
    return square_matrix::transpose(basis.a);
  }
  // O(n^3 + n^2 log(e)) (can use FFT for huge e)
  vector<vector<T>> middle(long long e = 1) const {
    assert(e >= 0);
    vector<vector<T>> frob(n, vector<T>(n, 0));
    for (int i = 0; i < len; ++i) {
      const int di = pt[i + 1] - pt[i];
      auto fs0 = mod_monic::power(e, pss[i]);
      fs0.resize(2 * di, 0);
      std::rotate(fs0.begin(), fs0.begin() + di, fs0.end());
      auto fs = fs0.begin() + di;
      for (int k = 0; k < di; ++k) {
        for (int l = 0; l < di; ++l) frob[pt[i] + l][pt[i] + k] = fs[l];
        --fs;
        for (int l = 0; l < di; ++l) fs[l] += pss[i][l] * fs[di];
      }
    }
    return frob;
  }
  // O(n^3 + n^2 log(e))
  vector<vector<T>> pow(long long e) const {
    return square_matrix::mul(left(), square_matrix::mul(middle(e), right()));
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include "modint.h"

using std::cerr;
using std::endl;

void unittest_Basis() {
  using Mint = ModInt<1'000'000'007>;
  constexpr int n = 4;
  Basis<Mint> basis(n);
  vector<vector<Mint>> b;
  auto add = [&](const vector<Mint> &us, bool extended) -> void {
    assert(basis.add(us) == extended);
    if (extended) b.push_back(us);
    assert(basis.n == n);
    assert(basis.size() == static_cast<int>(b.size()));
    assert(basis.b == b);
    assert(static_cast<int>(basis.a.size()) == n);
    for (int i = 0; i < n; ++i) assert(static_cast<int>(basis.a[i].size()) == n);
    assert(static_cast<int>(basis.c.size()) == n);
    for (int i = 0; i < n; ++i) assert(static_cast<int>(basis.c[i].size()) == n);
    for (int i = 0; i < n; ++i) {
      if (basis.c[i][i]) {
        for (int j = 0; j < i; ++j) assert(!basis.c[i][j]);
        assert(basis.c[i][i] == 1);
      } else {
        for (int j = 0; j < n; ++j) assert(!basis.c[i][j]);
      }
    }
    for (int i = 0; i < n; ++i) for (int j = 0; j < n; ++j) {
      Mint sum = 0;
      for (int k = 0; k < basis.size(); ++k) sum += basis.a[i][k] * basis.b[k][j];
      assert(sum == basis.c[i][j]);
      for (int k = basis.size(); k < n; ++k) assert(!basis.a[i][k]);
    }
    assert(static_cast<int>(basis.ps.size()) == basis.size());
    for (int j = 0; j < n; ++j) {
      Mint sum = 0;
      for (int k = 0; k < basis.size(); ++k) sum += basis.ps[k] * basis.b[k][j];
      assert(us[j] == sum);
    }
  };
  add({0, 0, 0, 0}, false);
  add({0, 3, 1, 4}, true);
  add({0, 6, 2, 1}, true);
  add({0, -3, -1, 10}, false);
  assert(basis.size() == 2);
  assert(basis.a == (vector<vector<Mint>>{
    {0, 0, 0, 0},
    {1/Mint(3), 0, 0, 0},
    {0, 0, 0, 0},
    {2/Mint(7), -1/Mint(7), 0, 0},
  }));
  assert(basis.b == (vector<vector<Mint>>{
    {0, 3, 1, 4},
    {0, 6, 2, 1},
  }));
  assert(basis.c == (vector<vector<Mint>>{
    {0, 0, 0, 0},
    {0, 1, 1/Mint(3), 4/Mint(3)},
    {0, 0, 0, 0},
    {0, 0, 0, 1},
  }));
  assert(basis.ps == (vector<Mint>{3, -2}));
  add({0, 5, 9, 2}, true);
  add({0, -5, -9, -2}, false);
  add({6, 5, 3, 5}, true);
  add({0, 0, 0, 0}, false);
  add({42, 14, -52, 49}, false);
  assert(basis.size() == 4);
  assert(basis.a == (vector<vector<Mint>>{
    {0, 0, 0, 1/Mint(6)},
    {1/Mint(3), 0, 0, 0},
    {-5/Mint(22), 0, 3/Mint(22), 0},
    {2/Mint(7), -1/Mint(7), 0, 0},
  }));
  assert(basis.b == (vector<vector<Mint>>{
    {0, 3, 1, 4},
    {0, 6, 2, 1},
    {0, 5, 9, 2},
    {6, 5, 3, 5},
  }));
  assert(basis.c == (vector<vector<Mint>>{
    {1, 5/Mint(6), 1/Mint(2), 5/Mint(6)},
    {0, 1, 1/Mint(3), 4/Mint(3)},
    {0, 0, 1, -7/Mint(11)},
    {0, 0, 0, 1},
  }));
  assert(basis.ps == (vector<Mint>{8, 0, -9, 7}));
  basis.reduce();
  assert(basis.size() == 4);
  assert(basis.a == (vector<vector<Mint>>{
    {-29/Mint(154), -3/Mint(154), -1/Mint(33), 1/Mint(6)},
    {-5/Mint(154), 17/Mint(77), -1/Mint(22), 0},
    {-1/Mint(22), -1/Mint(11), 3/Mint(22), 0},
    {2/Mint(7), -1/Mint(7), 0, 0},
  }));
  assert(basis.b == (vector<vector<Mint>>{
    {0, 3, 1, 4},
    {0, 6, 2, 1},
    {0, 5, 9, 2},
    {6, 5, 3, 5},
  }));
  assert(basis.c == (vector<vector<Mint>>{
    {1, 0, 0, 0},
    {0, 1, 0, 0},
    {0, 0, 1, 0},
    {0, 0, 0, 1},
  }));
}

// Depends on rng.
void unittest_Frobenius() {
  {
    using Mint = ModInt<1'000'000'007>;
    {
      const vector<vector<Mint>> a;
      const Frobenius<Mint> f(a);
      assert(f.n == 0);
      assert(f.len == 0);
      assert(f.pt == (vector<int>{0}));
      assert(f.pss == (vector<vector<Mint>>{}));
      assert(f.left() == (vector<vector<Mint>>{}));
      assert(f.middle() == (vector<vector<Mint>>{}));
      assert(f.right() == (vector<vector<Mint>>{}));
      assert(f.pow(0) == (vector<vector<Mint>>{}));
      assert(f.pow(1) == (vector<vector<Mint>>{}));
      assert(f.pow(2) == (vector<vector<Mint>>{}));
      assert(f.pow(58) == (vector<vector<Mint>>{}));
    }
    {
      // K[X]/(X-3)^2 (+) K[X]/(X-4) (+) K[X]/(X-4)
      const vector<vector<Mint>> a{
        {46, -123, 111, -33},
        {-26, 78, -73, 23},
        {-76, 219, -204, 64},
        {-108, 312, -294, 94},
      };
      const Frobenius<Mint> f(a);
      assert(f.n == 4);
      assert(f.len == 2);
      assert(f.pt == (vector<int>{0, 3, 4}));
      assert(f.pss == (vector<vector<Mint>>{{36, -33, 10}, {4}}));
      assert(f.middle() == (vector<vector<Mint>>{
        {0, 0, 36, 0},
        {1, 0, -33, 0},
        {0, 1, 10, 0},
        {0, 0, 0, 4},
      }));
      assert(f.pow(0) == (vector<vector<Mint>>{
        {1, 0, 0, 0},
        {0, 1, 0, 0},
        {0, 0, 1, 0},
        {0, 0, 0, 1},
      }));
      assert(f.pow(1) == a);
      assert(f.pow(2) == (vector<vector<Mint>>{
        {442, -1239, 1143, -345},
        {-160, 471, -450, 142},
        {-598, 1722, -1623, 505},
        {-888, 2562, -2424, 760}
      }));
      assert(f.pow(58) == (vector<vector<Mint>>{
        {741105202, 153013355, 126691176, 542400778},
        {573751924, 609663784, 160047185, 762973231},
        {299460375, 561397282, 636293578, 738643668},
        {450144711, 412471395, 151172802, 937497940},
      }));
    }
  }
  {
    using Mint = ModInt<2>;
    for (int n = 1; n <= 4; ++n) {
      for (int p = 0; p < 1 << n; ++p) {
        vector<vector<Mint>> a(n, vector<Mint>(n));
        for (int i = 0; i < n; ++i) for (int j = 0; j < n; ++j) {
          a[i][j] = p >> (i * n + j) & 1;
        }
        const Frobenius<Mint> f(a);
        assert(f.pow(1) == a);
        assert(f.pow(2) == square_matrix::mul(a, a));
        assert(f.pow(3) == square_matrix::mul(a, square_matrix::mul(a, a)));
      }
    }
  }
}

int main() {
  unittest_Basis(); cerr << "PASSED unittest_Basis" << endl;
  unittest_Frobenius(); cerr << "PASSED unittest_Frobenius" << endl;
  return 0;
}
