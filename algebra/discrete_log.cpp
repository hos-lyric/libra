#include <math.h>

// Map: T -> int
// F: monoid
// T: set
// *: F * T -> T: action
// Returns min e \in [0, n) s.t. f^e a = b, or -1 if no such e exists.
// injective can be set true if f is injective on {f^* a, f^* b}.
template <class Map, class F, class T>
long long discreteLog(F f, T a, T b, long long n, bool injective) {
  if (n <= 0) return -1;
  const int m = ceill(sqrtl(n));
  Map rs;
  T bb = b;
  for (int r = 1; r <= m; ++r) rs[bb = f * bb] = r;
  const F fm = f.pow(m);
  int counter = 0;
  for (int q = 0; q < m; ++q) {
    const T aa = fm * a;
    auto it = rs.find(aa);
    if (it != rs.end()) {
      if (injective) {
        const long long e = static_cast<long long>(m) * q + (m - it->second);
        return (e < n) ? e : -1;
      } else {
        for (int r = 0; r < m; ++r) {
          if (a == b) {
            const long long e = static_cast<long long>(m) * q + r;
            return (e < n) ? e : -1;
          }
          a = f * a;
        }
        if (++counter >= 2) break;
      }
    }
    a = aa;
  }
  return -1;
}

////////////////////////////////////////////////////////////////////////////////

#include <assert.h>
#include <iostream>
#include <map>
#include <random>
#include <unordered_map>
#include <vector>

using std::cerr;
using std::endl;
using std::map;
using std::mt19937_64;
using std::unordered_map;
using std::vector;

// ... -> -1 -> 0 -> 1 -> ... -> m-1 -> 0
struct Rho {
  long long m, step;
  Rho pow(long long e) const {
    return Rho{m, e * step};
  }
  long long operator*(long long a) const {
    assert(a < m);
    const long long b = a + step;
    return (b < 0) ? b : (b % m);
  }
};

void unittest() {
  {
    constexpr int LIM_SMALL = 50;
    for (int m = 1; m <= LIM_SMALL; ++m) {
      const Rho f{m, 1};
      for (int a = -LIM_SMALL; a <= 0; ++a) {
        for (int b = -LIM_SMALL; b < m; ++b) {
          const int e = (a <= b) ? (b - a) : -1;
          for (int n = 0; n <= LIM_SMALL; ++n) {
            assert((discreteLog<map<int, int>>(f, a, b, n, false)) == ((e < n) ? e : -1));
          }
          if (a >= 0 && b >= 0) {
            for (int n = 0; n <= LIM_SMALL; ++n) {
              assert((discreteLog<map<int, int>>(f, a, b, n, true)) == ((e < n) ? e : -1));
            }
          }
        }
      }
    }
  }
  {
    using Map = unordered_map<long long, int>;
    constexpr int NUM_CASES = 100;
    constexpr long long LIM_LARGE = 10'000'000'000LL;
    mt19937_64 rng;
    for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
      const long long m = 1 + rng() % LIM_LARGE;
      const Rho f{m, 1};
      const long long a = -LIM_LARGE + rng() % (LIM_LARGE + 1);
      const long long b = -LIM_LARGE + rng() % (LIM_LARGE + m);
      if (a <= b) {
        const long long e = b - a;
        assert((discreteLog<Map>(f, a, b, e, false)) == -1);
        assert((discreteLog<Map>(f, a, b, e + 1, false)) == e);
        assert((discreteLog<Map>(f, a, b, 2 * LIM_LARGE, false)) == e);
      } else {
        assert((discreteLog<Map>(f, a, b, LIM_LARGE, false)) == -1);
      }
    }
    for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
      const long long m = 1 + rng() % LIM_LARGE;
      const Rho f{m, 1};
      const long long a = 0;
      const long long b = rng() % m;
      const long long e = b - a;
      assert((discreteLog<Map>(f, a, b, e, true)) == -1);
      assert((discreteLog<Map>(f, a, b, e + 1, true)) == e);
      assert((discreteLog<Map>(f, a, b, LIM_LARGE, true)) == e);
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
