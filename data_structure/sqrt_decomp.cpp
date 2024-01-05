#include <assert.h>
#include <math.h>
#include <algorithm>
#include <vector>

using std::max;
using std::vector;

// get i
// add val to [a, b)
// count < val in [a, b)
// O(sqrt(n) log(n)) per query
template <class T> struct RangeAddRangeCount {
  int n, l, m;
  vector<T> ts, offset, sorted;
  RangeAddRangeCount() {}
  RangeAddRangeCount(const vector<T> &ts_) : ts(ts_) {
    n = ts.size();
    m = max<int>(sqrt(n), 1);
    l = n / m;
    offset.assign(l + 1, 0);
    sorted.resize(l * m);
    for (int x = 0; x < l; ++x) build(x);
  }
  void build(int x) {
    assert(0 <= x); assert(x < l);
    std::copy(ts.begin() + (x * m), ts.begin() + ((x + 1) * m), sorted.begin() + (x * m));
    std::sort(sorted.begin() + (x * m), sorted.begin() + ((x + 1) * m));
  }
  T operator[](int i) const {
    assert(0 <= i); assert(i < n);
    return offset[i / m] + ts[i];
  }
  void add(int a, int b, T val) {
    assert(0 <= a); assert(a <= b); assert(b <= n);
    const int xA = (a + m - 1) / m;
    const int xB = b / m;
    if (xA <= xB) {
      for (int i = xA * m; --i >= a; ) ts[i] += val;
      if (xA > 0) build(xA - 1);
      for (int x = xA; x < xB; ++x) offset[x] += val;
      for (int i = xB * m; i < b; ++i) ts[i] += val;
      if (xB < l) build(xB);
    } else {
      for (int i = a; i < b; ++i) ts[i] += val;
      if (xB < l) build(xB);
    }
  }
  int count(int a, int b, T val) const {
    assert(0 <= a); assert(a <= b); assert(b <= n);
    const int xA = (a + m - 1) / m;
    const int xB = b / m;
    int cnt = 0;
    if (xA <= xB) {
      for (int i = xA * m; --i >= a; ) if (offset[xA - 1] + ts[i] < val) ++cnt;
      for (int x = xA; x < xB; ++x) {
        cnt += (lower_bound(sorted.begin() + (x * m), sorted.begin() + ((x + 1) * m), val - offset[x]) - (sorted.begin() + (x * m)));
      }
      for (int i = xB * m; i < b; ++i) if (offset[xB] + ts[i] < val) ++cnt;
    } else {
      for (int i = a; i < b; ++i) if (offset[xB] + ts[i] < val) ++cnt;
    }
    return cnt;
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <utility>

using std::cerr;
using std::endl;
using std::swap;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void unittest() {
  constexpr int NUM_QUERIES = 100'000;
  for (int n = 1; n <= 100; ++n) {
    vector<long long> brt(n);
    for (int i = 0; i < n; ++i) brt[i] = static_cast<int>(xrand());
    RangeAddRangeCount<long long> f(brt);
    for (int i = 0; i < n; ++i) assert(f[i] == brt[i]);
    for (int q = 0; q < NUM_QUERIES; ++q) {
      int a = xrand() % (n + 1);
      int b = xrand() % (n + 1);
      if (a > b) swap(a, b);
      const long long val = static_cast<int>(xrand());
      if (xrand() & 1) {
        f.add(a, b, val);
        for (int i = a; i < b; ++i) brt[i] += val;
      } else {
        const int actual = f.count(a, b, val);
        int expected = 0;
        for (int i = a; i < b; ++i) if (brt[i] < val) ++expected;
        assert(actual == expected);
      }
      for (int i = 0; i < n; ++i) assert(f[i] == brt[i]);
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
