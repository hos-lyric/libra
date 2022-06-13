#include <assert.h>
#include <map>

using std::map;

//      k[0]    k[1]  ...       k[n-1]=kLim
// ------)[------)[-  ...  -)[------)[unpainted
//  v[0]    v[1]              v[n-1]
template <class K, class V> struct Painter : map<K, V> {
  const K kLim;
  Painter(K k, const V &v) : map<K, V>{{k, v}}, kLim(k) {}
  // Paint [a, b) with v, calling f(left, right, (old color)).
  template <class F> void paint(K a, K b, const V &v, F f) {
    assert(a < b); assert(b < kLim);
    auto it = this->lower_bound(a);
    if (b < it->first) {
      f(a, b, it->second);
      this->emplace(a, it->second);
      this->emplace(b, v);
    } else if (a < it->first) {
      const V va = it->second;
      K k = a;
      for (; it->first <= b; it = this->erase(it)) {
        f(k, it->first, it->second);
        k = it->first;
      }
      if (k < b) {
        f(k, b, it->second);
      }
      this->emplace(a, va);
      this->emplace(b, v);
    } else {
      ++it;
      K k = a;
      for (; it->first <= b; it = this->erase(it)) {
        f(k, it->first, it->second);
        k = it->first;
      }
      if (k < b) {
        f(k, b, it->second);
      }
      this->emplace(b, v);
    }
  }
  void paint(K a, K b, const V &v) {
    paint(a, b, v, [&](K, K, const V &) -> void {});
  }
  V get(K k) const {
    assert(k < kLim);
    return this->upper_bound(k)->second;
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <string>
#include <vector>

using std::string;
using std::vector;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void unittest() {
  {
    Painter<int, string> painter(10, "-1");
    assert(painter == (map<int, string>{{10, "-1"}}));
    painter.paint(0, 5, "-2");
    assert(painter == (map<int, string>{{0, "-1"}, {5, "-2"}, {10, "-1"}}));
    painter.paint(3, 6, "-3");
    assert(painter == (map<int, string>{{0, "-1"}, {3, "-2"}, {6, "-3"}, {10, "-1"}}));
    painter.paint(4, 8, "-4");
    assert(painter == (map<int, string>{{0, "-1"}, {3, "-2"}, {4, "-3"}, {8, "-4"}, {10, "-1"}}));
    painter.paint(2, 7, "-5");
    assert(painter == (map<int, string>{{0, "-1"}, {2, "-2"}, {7, "-5"}, {8, "-4"}, {10, "-1"}}));
    painter.paint(5, 9, "-6");
    assert(painter == (map<int, string>{{0, "-1"}, {2, "-2"}, {5, "-5"}, {9, "-6"}, {10, "-1"}}));
    painter.paint(2, 7, "-7");
    assert(painter == (map<int, string>{{0, "-1"}, {2, "-2"}, {7, "-7"}, {9, "-6"}, {10, "-1"}}));
    painter.paint(5, 9, "-8");
    assert(painter == (map<int, string>{{0, "-1"}, {2, "-2"}, {5, "-7"}, {9, "-8"}, {10, "-1"}}));
    painter.paint(1, 5, "-9");
    assert(painter == (map<int, string>{{0, "-1"}, {1, "-2"}, {5, "-9"}, {9, "-8"}, {10, "-1"}}));
  }
  for (int caseId = 0; caseId < 1000; ++caseId) {
    const int n = 1 + xrand() % 1000;
    vector<int> brt(n, -1), sol(n, -1);
    Painter<int, int> painter(n + 1, -1);
    for (int queryId = 0; queryId < 1000; ++queryId) {
      for (; ; ) {
        const int a = xrand() % (n + 1);
        const int b = xrand() % (n + 1);
        if (a < b) {
          for (int i = a; i < b; ++i) {
            brt[i] = queryId;
          }
          painter.paint(a, b, queryId, [&](int l, int r, int old) -> void {
            assert(0 <= l); assert(l < r); assert(r <= n);
            for (int i = l; i < r; ++i) {
              assert(sol[i] == old);
              sol[i] = queryId;
            }
          });
          for (int i = 0; i < n; ++i) {
            assert(sol[i] == painter.get(i));
          }
          assert(brt == sol);
          break;
        }
      }
    }
  }
}

int main() {
  unittest();
  return 0;
}
