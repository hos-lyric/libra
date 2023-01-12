// C++17 for unittest

#include <assert.h>
#include <utility>
#include <vector>

using std::make_pair;
using std::pair;
using std::swap;
using std::vector;

// a x + b y = (+/-) gcd(a, b)
//   (a, 0): g = a, x = 1, y = 0
//   (0, b), (b, b), (-b, b) (b != 0): g = b, x = 0, y = 1
//   otherwise: 2 |x| <= |b|, 2 |y| <= |a|
// T: int, long long, __int128
template <class S> S gojo(S a, S b, S &x, S &y) {
  if (b != 0) {
    const S g = gojo(b, a % b, y, x);
    y -= (a / b) * x;
    return g;
  } else {
    x = 1;
    y = 0;
    return a;
  }
}

// x == bs[i]  (mod ms[i])
// S: signed integer
template <class S>
pair<S, S> modSystem(const vector<S> &ms, const vector<S> &bs) {
  const int len = ms.size();
  assert(static_cast<size_t>(len) == bs.size());
  S m0 = 1, b0 = 0;
  for (int i = 0; i < len; ++i) {
    assert(ms[i] >= 1);
    S m1 = ms[i], b1 = bs[i];
    if ((b1 %= m1) < 0) b1 += m1;
    if (m0 < m1) {
      swap(m0, m1);
      swap(b0, b1);
    }
    // to avoid overflow
    if (m0 % m1 == 0) {
      if (b0 % m1 != b1) return make_pair(0, 0);
      continue;
    }
    S z0, z1;
    const S g = gojo(m0, m1, z0, z1);
    b1 -= b0;
    if (b1 % g != 0) return make_pair(0, 0);
    (b1 /= g) %= m1;
    m1 /= g;
    b0 += m0 * ((z0 * b1) % m1);
    m0 *= m1;
    if (b0 < 0) b0 += m0;
  }
  return make_pair(m0, b0);
}

// TODO: modSystem(ms, as, bs)

////////////////////////////////////////////////////////////////////////////////

#include <math.h>
#include <iostream>
#include <numeric>

using std::cerr;
using std::endl;

void unittest_gojo() {
  {
    int x, y;
    assert(gojo(39, 15, x, y) == 3);
    assert(x == 2);
    assert(y == -5);
  }
  // TODO: test large values
  {
    using Int = long long;
    constexpr Int lim = 1000;
    for (Int a = -lim; a <= lim; ++a) for (Int b = -lim; b <= lim; ++b) {
      Int x, y;
      const Int g = gojo(a, b, x, y);
      assert(abs(g) == std::gcd(a, b));
      assert(a * x + b * y == g);
      if (b == 0) {
        assert(g == a);
        assert(x == 1);
        assert(y == 0);
      } else if (a == 0 || abs(a) == abs(b)) {
        assert(g == b);
        assert(x == 0);
        assert(y == 1);
      } else {
        assert(2 * abs(x) <= abs(b));
        assert(2 * abs(y) <= abs(a));
      }
    }
  }
}

void unittest_modSystem() {
  assert(modSystem<int>({6, 10}, {13, -1}) == make_pair(30, 19));
  assert(modSystem<int>({6, 10}, {5, 8}) == make_pair(0, 0));
  // TODO: test large values
  {
    using Int = long long;
    constexpr Int lim = 100;
    for (Int m0 = 1; m0 <= lim; ++m0) for (Int b0 = -lim; b0 <= lim; ++b0) {
      const pair<Int, Int> res = modSystem<Int>({m0}, {b0});
      assert(res.first == m0);
      assert(0 <= res.second); assert(res.second < m0);
      assert((res.second - b0) % m0 == 0);
    }
  }
  {
    using Int = long long;
    constexpr Int lim = 50;
    for (Int m0 = 1; m0 <= lim; ++m0) for (Int m1 = 1; m1 <= lim; ++m1) {
      const Int l = m0 / std::gcd(m0, m1) * m1;
      vector<vector<Int>> tab(m0, vector<Int>(m1, -1));
      for (Int x = 0; x < l; ++x) {
        tab[x % m0][x % m1] = x;
      }
      for (Int b0 = -lim; b0 <= lim; ++b0) for (Int b1 = -lim; b1 <= lim; ++b1) {
        const Int x = tab[(b0 % m0 + m0) % m0][(b1 % m1 + m1) % m1];
        const pair<Int, Int> res = modSystem<Int>({m0, m1}, {b0, b1});
        if (~x) {
          assert(res.first == l);
          assert(res.second == x);
        } else {
          assert(res.first == 0);
          assert(res.second == 0);
        }
      }
    }
  }
  {
    using Int = long long;
    constexpr Int lim = 20;
    for (Int m0 = 1; m0 <= lim; ++m0) for (Int m1 = 1; m1 <= lim; ++m1) for (Int m2 = 1; m2 <= lim; ++m2) {
      Int l = m0 / std::gcd(m0, m1) * m1;
      l = l / std::gcd(l, m2) * m2;
      vector<vector<vector<Int>>> tab(m0, vector<vector<Int>>(m1, vector<Int>(m2, -1)));
      for (Int x = 0; x < l; ++x) {
        tab[x % m0][x % m1][x % m2] = x;
      }
      for (Int b0 = 0; b0 < m0; ++b0) for (Int b1 = 0; b1 < m1; ++b1) for (Int b2 = 0; b2 < m2; ++b2) {
        const Int x = tab[b0][b1][b2];
        const pair<Int, Int> res = modSystem<Int>({m0, m1, m2}, {b0, b1, b2});
        if (~x) {
          assert(res.first == l);
          assert(res.second == x);
        } else {
          assert(res.first == 0);
          assert(res.second == 0);
        }
      }
    }
  }
}

int main() {
  unittest_gojo(); cerr << "PASSED unittest_gojo" << endl;
  unittest_modSystem(); cerr << "PASSED unittest_modSystem" << endl;
  return 0;
}
