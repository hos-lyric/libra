#include <assert.h>

using Int = long long;

// l = min {  (+a x) mod m  |  1 <= x <= n  }
// r = min {  (-a y) mod m  |  1 <= y <= n  }
// three-gap (l > 0 && r > 0)
//   l    : (a 0, a x), ..., (a (n - x), a n)
//   l + r: (a (n - x + 1), a (n - y + 1)), ..., (a (y - 1), a (x - 1))
//       r: (a y, a 0), ..., (a n, a (n - y))
struct MinMaxRem {
  Int l, r, x, y;
  MinMaxRem(Int m, Int a, Int n) {
    assert(m >= 1); assert(0 <= a); assert(a < m); assert(n >= 1);
    l = a; r = m - a; x = 1; y = 1;
    for (Int k, k0; ; ) {
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

#include <map>

using std::map;

void unittestMinMaxRem() {
  {
    // 7, 14, 5, 12, 3, 10
    MinMaxRem rem(16, 7, 6);
    assert(rem.l == 3);
    assert(rem.r == 2);
    assert(rem.x == 5);
    assert(rem.y == 2);
  }
  {
    auto test = [&](Int m, Int a, Int n0, bool testGap) -> void {
      Int l = m + 1, r = m + 1, x = 0, y = 0;
      map<Int, Int> ps;
      ps[0] = ps[m] = 0;
      for (Int n = 1; n <= n0; ++n) {
        const Int an = (static_cast<__int128>(a) * n) % m;
        if (l > an) { l = an; x = n; }
        const Int bn = an ? (m - an) : 0;
        if (r > bn) { r = bn; y = n; }
        const MinMaxRem rem(m, a, n);
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
    test(1001001001001001001, 123456789012345678, 1234567, false);
  }
}

int main() {
  unittestMinMaxRem();
  return 0;
}
