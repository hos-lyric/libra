#include <assert.h>
#include <utility>

using std::swap;

// l = min {  (+a x) mod m  |  1 <= x <= n  }
// r = min {  (-a y) mod m  |  1 <= y <= n  }
// three-gap (l > 0 && r > 0)
//   l    : (a 0, a x), ..., (a (n - x), a n)
//   l + r: (a (n - x + 1), a (n - y + 1)), ..., (a (y - 1), a (x - 1))
//       r: (a y, a 0), ..., (a n, a (n - y))
// S: (unsigned or signed) integer
template <class S> struct MinMaxRem {
  S l, r, x, y;
  MinMaxRem(S m, S a, S n) {
    assert(m >= 1); assert(0 <= a); assert(a < m); assert(n >= 1);
    l = a; r = m - a; x = 1; y = 1;
    for (S k, k0; ; ) {
      if (!l) { r = 0; y = x; return; }
      k = r / l; k0 = (n - y) / x;
      if (k > k0) { r -= k0 * l; y += k0 * x; return; }
      r -= k * l; y += k * x;
      if (!r) { l = 0; x = y; return; }
      k = l / r; k0 = (n - x) / y;
      if (k > k0) { l -= k0 * r; x += k0 * y; return; }
      l -= k * r; x += k * y;
    }
  }
};

////////////////////////////////////////////////////////////////////////////////

// y^f(0) x y^(f(1)-f(0)) x y^(f(2)-f(1)) x ... x y^(f(n)-f(n-1))
//   where f(i) = floor((a i + b) / m)
// S: (unsigned or signed) integer
//   (a n + b) and (m + a) does not overflow
// T: monoid with pow
//   e: identity
template <class S, class T> T pathUnder(S m, S a, S b, S n, T e, T x, T y) {
  assert(m >= 1); assert(a >= 0); assert(b >= 0); assert(n >= 0);
  S c = (a * n + b) / m;
  T pre = e, suf = e;
  for (; ; ) {
    const S p = a / m; a %= m; x = x * y.pow(p);
    const S q = b / m; b %= m; pre = pre * y.pow(q);
    c -= (p * n + q);
    if (c == 0) return pre * x.pow(n) * suf;
    const S d = (m * c - b - 1) / a + 1;
    suf = y * x.pow(n - d) * suf;
    b = m - b - 1 + a; swap(m, a); n = c - 1; c = d; swap(x, y);
  }
}

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <map>
#include <string>

using std::cerr;
using std::endl;
using std::map;
using std::string;

void unittest_MinMaxRem() {
  {
    // 7, 14, 5, 12, 3, 10
    MinMaxRem<unsigned> rem(16, 7, 6);
    assert(rem.l == 3);
    assert(rem.r == 2);
    assert(rem.x == 5);
    assert(rem.y == 2);
  }
  {
    using Int = long long;
    auto test = [&](Int m, Int a, Int n0, bool testGap) -> void {
      Int l = m + 1, r = m + 1, x = 0, y = 0;
      map<Int, Int> ps;
      ps[0] = ps[m] = 0;
      for (Int n = 1; n <= n0; ++n) {
        const Int an = (static_cast<__int128>(a) * n) % m;
        if (l > an) { l = an; x = n; }
        const Int bn = an ? (m - an) : 0;
        if (r > bn) { r = bn; y = n; }
        const MinMaxRem<Int> rem(m, a, n);
        assert(rem.l == l);
        assert(rem.r == r);
        assert(rem.x == x);
        assert(rem.y == y);
        if (testGap && l > 0 && r > 0) {
          ps[an] = n;
          for (auto it = ps.begin(); it->first < m; ++it) {
            auto it1 = it; ++it1;
            const Int gap = it1->first - it->first;
            const Int i = it->second, j = it1->second;
            if (0 <= i && i <= n - x) {
              assert(gap == l);
              assert(j - i == x);
            } else if (n - x - 1 <= i && i <= y - 1) {
              assert(gap == l + r);
              assert(j - i == x - y);
            } else if (y <= i && i <= n) {
              assert(gap == r);
              assert(j - i == -y);
            }
          }
        }
      }
    };
    for (Int m = 1; m <= 100; ++m) for (Int a = 0; a < m; ++a) {
      test(m, a, 100, true);
    }
    test(123456789, 98765432, 1234567, false);
    test(1001001001001001001LL, 123456789012345678LL, 1234567, false);
  }
}

struct StringMonoid {
  string s;
  StringMonoid operator*(const StringMonoid &a) { return {s + a.s}; }
  StringMonoid pow(int e) {
    assert(e >= 0);
    string ss;
    for (int i = 0; i < e; ++i) ss += s;
    return {ss};
  }
};
void unittest_pathUnder() {
  const StringMonoid e{""}, x{"x"}, y{"y"};
  {
    // 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3
    assert(pathUnder<unsigned long long>(10, 3, 2, 12, e, x, y).s ==
           "xxxyxxxyxxxxyxx");
  }
  {
    constexpr int lim = 30;
    for (int m = 1; m <= lim; ++m) {
      for (int a = 0; a <= lim; ++a) for (int b = 0; b <= lim; ++b) {
        string s((a * 0 + b) / m, 'y');
        for (int n = 0; n <= lim; ++n) {
          if (n > 0) {
            s += 'x';
            s += string((a * n + b) / m - (a * (n - 1) + b) / m, 'y');
          }
          assert(pathUnder<unsigned>(m, a, b, n, e, x, y).s == s);
        }
      }
    }
  }
}

int main() {
  unittest_MinMaxRem(); cerr << "PASSED unittest_MinMaxRem" << endl;
  unittest_pathUnder(); cerr << "PASSED unittest_pathUnder" << endl;
  return 0;
}
