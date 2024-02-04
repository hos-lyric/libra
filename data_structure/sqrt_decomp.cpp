#include <assert.h>
#include <math.h>
#include <algorithm>
#include <vector>

using std::max;
using std::min;
using std::vector;

// add val to a: O(sqrt(n))
// get sum of [a, b): O(1)
template <class T> struct PointAddRangeSum {
  int n, l, e;
  vector<T> giant, baby;
  PointAddRangeSum() {}
  PointAddRangeSum(int n_) : n(n_) {
    for (e = 0; 1 << (2 * e) < n; ++e) {}
    l = n >> e;
    giant.assign(l + 1, T());
    baby.assign(n + 1, T());
  }
  PointAddRangeSum(const vector<T> &ts) {
    n = ts.size();
    for (e = 0; 1 << (2 * e) < n; ++e) {}
    l = n >> e;
    giant.assign(l + 1, T());
    baby.assign(n + 1, T());
    T sumsum = T();
    for (int x = 0; x <= l; ++x) {
      giant[x] = sumsum;
      const int limY = min((x + 1) << e, n + 1);
      T sum = T();
      for (int y = x << e; y < limY; ++y) {
        baby[y] = sum;
        if (y < n) sum += ts[y];
      }
      sumsum += sum;
    }
  }
  void add(int a, T val) {
    assert(0 <= a); assert(a < n);
    for (int x = (a >> e) + 1; x <= l; ++x) giant[x] += val;
    const int limY = min(((a >> e) + 1) << e, n + 1);
    for (int y = a + 1; y < limY; ++y) baby[y] += val;
  }
  inline T get(int a) const {
    return giant[a >> e] + baby[a];
  }
  inline T get(int a, int b) const {
    return get(b) - get(a);
  }
};

////////////////////////////////////////////////////////////////////////////////

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
    offset.assign(l + 1, T());
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
#include <random>
#include <utility>

using std::cerr;
using std::endl;
using std::mt19937_64;
using std::swap;

void unittest_PointAddRangeSum() {
  {
    PointAddRangeSum<unsigned> f(0);
    assert(f.get(0) == 0);
    assert(f.get(0, 0) == 0);
  }
  constexpr int MAX_N = 1'000;
  constexpr int NUM_QUERIES = 1'000;
  mt19937_64 rng;
  for (int n = 1; n <= MAX_N; ++n) {
    vector<long long> brt(n);
    PointAddRangeSum<long long> f(n);
    for (int q = 0; q < NUM_QUERIES; ++q) {
      if (rng() & 1) {
        const int a = rng() % n;
        const long long val = static_cast<int>(rng());
        brt[a] += val;
        f.add(a, val);
      } else {
        int a = rng() % (n + 1);
        int b = rng() % (n + 1);
        if (a > b) swap(a, b);
        long long expected = 0;
        for (int i = a; i < b; ++i) expected += brt[i];
        assert(f.get(a, b) == expected);
      }
    }
  }
  for (int n = 1; n <= MAX_N; ++n) {
    vector<long long> brt(n);
    for (int i = 0; i < n; ++i) brt[i] = static_cast<int>(rng());
    PointAddRangeSum<long long> f(brt);
    for (int q = 0; q < NUM_QUERIES; ++q) {
      if (rng() & 1) {
        const int a = rng() % n;
        const long long val = static_cast<int>(rng());
        brt[a] += val;
        f.add(a, val);
      } else {
        int a = rng() % (n + 1);
        int b = rng() % (n + 1);
        if (a > b) swap(a, b);
        long long expected = 0;
        for (int i = a; i < b; ++i) expected += brt[i];
        assert(f.get(a, b) == expected);
      }
    }
  }
}

void unittest_RangeAddRangeCount() {
  constexpr int MAX_N = 100;
  constexpr int NUM_QUERIES = 10'000;
  mt19937_64 rng;
  for (int n = 0; n <= MAX_N; ++n) {
    vector<long long> brt(n);
    for (int i = 0; i < n; ++i) brt[i] = static_cast<int>(rng());
    RangeAddRangeCount<long long> f(brt);
    for (int i = 0; i < n; ++i) assert(f[i] == brt[i]);
    for (int q = 0; q < NUM_QUERIES; ++q) {
      int a = rng() % (n + 1);
      int b = rng() % (n + 1);
      if (a > b) swap(a, b);
      const long long val = static_cast<int>(rng());
      if (rng() & 1) {
        for (int i = a; i < b; ++i) brt[i] += val;
        f.add(a, b, val);
      } else {
        int expected = 0;
        for (int i = a; i < b; ++i) if (brt[i] < val) ++expected;
        assert(f.count(a, b, val) == expected);
      }
      for (int i = 0; i < n; ++i) assert(f[i] == brt[i]);
    }
  }
}

int main() {
  unittest_PointAddRangeSum(); cerr << "PASSED unittest_PointAddRangeSum" << endl;
  unittest_RangeAddRangeCount(); cerr << "PASSED unittest_RangeAddRangeCount" << endl;
  return 0;
}
