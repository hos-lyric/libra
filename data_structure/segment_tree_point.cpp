#include <assert.h>
#include <vector>

using std::vector;

// T: monoid representing information of an interval.
//   T()  should return the identity.
//   T(S s)  should represent a single element of the array.
//   T::pull(const T &l, const T &r)  should pull two intervals.
template <class T> struct SegmentTreePoint {
  int logN, n;
  vector<T> ts;
  SegmentTreePoint() : logN(0), n(0) {}
  explicit SegmentTreePoint(int n_) {
    for (logN = 0, n = 1; n < n_; ++logN, n <<= 1) {}
    ts.resize(n << 1);
  }
  template <class S> explicit SegmentTreePoint(const vector<S> &ss) {
    const int n_ = ss.size();
    for (logN = 0, n = 1; n < n_; ++logN, n <<= 1) {}
    ts.resize(n << 1);
    for (int i = 0; i < n_; ++i) at(i) = T(ss[i]);
    build();
  }
  T &at(int i) {
    return ts[n + i];
  }
  void build() {
    for (int u = n; --u; ) pull(u);
  }

  inline void pull(int u) {
    ts[u].pull(ts[u << 1], ts[u << 1 | 1]);
  }

  // Changes the value of point a to s.
  template <class S> void change(int a, const S &s) {
    assert(0 <= a); assert(a < n);
    ts[a += n] = T(s);
    for (; a >>= 1; ) pull(a);
  }

  // Applies T::f(args...) to point a.
  template <class F, class... Args>
  void ch(int a, F f, Args &&... args) {
    assert(0 <= a); assert(a < n);
    (ts[a += n].*f)(args...);
    for (; a >>= 1; ) pull(a);
  }

  // Calculates the product for [a, b).
  T get(int a, int b) {
    assert(0 <= a); assert(a <= b); assert(b <= n);
    if (a == b) return T();
    T prodL, prodR, t;
    for (a += n, b += n; a < b; a >>= 1, b >>= 1) {
      if (a & 1) { t.pull(prodL, ts[a++]); prodL = t; }
      if (b & 1) { t.pull(ts[--b], prodR); prodR = t; }
    }
    t.pull(prodL, prodR);
    return t;
  }

  // Calculates T::f(args...) of a monoid type for [a, b).
  //   op(-, -)  should calculate the product.
  //   e()  should return the identity.
  template <class Op, class E, class F, class... Args>
#if __cplusplus >= 201402L
  auto
#else
  decltype((std::declval<T>().*F())())
#endif
  get(int a, int b, Op op, E e, F f, Args &&... args) {
    assert(0 <= a); assert(a <= b); assert(b <= n);
    if (a == b) return e();
    auto prodL = e(), prodR = e();
    for (a += n, b += n; a < b; a >>= 1, b >>= 1) {
      if (a & 1) prodL = op(prodL, (ts[a++].*f)(args...));
      if (b & 1) prodR = op((ts[--b].*f)(args...), prodR);
    }
    return op(prodL, prodR);
  }

  // Find min b s.t. T::f(args...) returns true,
  // when called for the partition of [a, b) from left to right.
  //   Returns n + 1 if there is no such b.
  template <class F, class... Args>
  int findRight(int a, F f, Args &&... args) {
    assert(0 <= a); assert(a <= n);
    if ((T().*f)(args...)) return a;
    if (a == n) return n + 1;
    a += n;
    for (; ; a >>= 1) if (a & 1) {
      if ((ts[a].*f)(args...)) {
        for (; a < n; ) {
          if (!(ts[a <<= 1].*f)(args...)) ++a;
        }
        return a - n + 1;
      }
      ++a;
      if (!(a & (a - 1))) return n + 1;
    }
  }

  // Find max a s.t. T::f(args...) returns true,
  // when called for the partition of [a, b) from right to left.
  //   Returns -1 if there is no such a.
  template <class F, class... Args>
  int findLeft(int b, F f, Args &&... args) {
    assert(0 <= b); assert(b <= n);
    if ((T().*f)(args...)) return b;
    if (b == 0) return -1;
    b += n;
    for (; ; b >>= 1) if ((b & 1) || b == 2) {
      if ((ts[b - 1].*f)(args...)) {
        for (; b <= n; ) {
          if (!(ts[(b <<= 1) - 1].*f)(args...)) --b;
        }
        return b - n - 1;
      }
      --b;
      if (!(b & (b - 1))) return -1;
    }
  }
};  // SegmentTreePoint<T>

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <algorithm>
#include <iostream>

using std::cerr;
using std::endl;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

////////////////////////////////////////////////////////////////////////////////

namespace point_change_range_min_range_max {
//   update point  a[i] <- b
//   get  min a[l, r)
//   get  max a[l, r)

constexpr long long INF = 1001001001001001001LL;

using std::max;
using std::min;

struct Node {
  long long mn, mx;
  Node() : mn(INF), mx(-INF) {}
  Node(long long val) : mn(val), mx(val) {}
  void pull(const Node &l, const Node &r) {
    mn = min(l.mn, r.mn);
    mx = max(l.mx, r.mx);
  }
  void ch(long long val) {
    mn = mx = val;
  }
  long long getMin() const {
    return mn;
  }
  long long getMax() const {
    return mx;
  }
  bool accMin(long long &acc, long long tar) const {
    if (tar >= mn) return true;
    if (acc > mn) acc = mn;
    return false;
  }
  bool accMax(long long &acc, long long tar) const {
    if (tar <= mx) return true;
    if (acc < mx) acc = mx;
    return false;
  }
};

long long getMin(SegmentTreePoint<Node> &seg, int a, int b) {
  return seg.get(a, b,
                 [&](long long l, long long r) -> long long { return min(l, r); },
                 [&]() -> long long { return INF; },
                 &Node::getMin);
}
long long getMax(SegmentTreePoint<Node> &seg, int a, int b) {
  return seg.get(a, b,
                 [&](long long l, long long r) -> long long { return max(l, r); },
                 [&]() -> long long { return -INF; },
                 &Node::getMax);
}

// (min of [a, b)) <= target
int findRightMin(SegmentTreePoint<Node> &seg, int a, long long tar) {
  long long acc = INF;
  return seg.findRight(a, &Node::accMin, acc, tar);
}
int findLeftMin(SegmentTreePoint<Node> &seg, int b, long long tar) {
  long long acc = INF;
  return seg.findLeft(b, &Node::accMin, acc, tar);
}

// (max of [a, b)) >= target
int findRightMax(SegmentTreePoint<Node> &seg, int a, long long tar) {
  long long acc = -INF;
  return seg.findRight(a, &Node::accMax, acc, tar);
}
int findLeftMax(SegmentTreePoint<Node> &seg, int b, long long tar) {
  long long acc = -INF;
  return seg.findLeft(b, &Node::accMax, acc, tar);
}

void unittest() {
  // small
  {
    SegmentTreePoint<Node> seg(vector<long long>{1, 2, 3, 4, 5});
    // [1, 2, 3, 4, 5]
    assert(getMin(seg, 0, 5) == 1);
    assert(getMax(seg, 0, 5) == 5);
    assert(findRightMin(seg, 1, 4) == 2);
    assert(findLeftMin(seg, 3, 2) == 1);
    assert(findRightMax(seg, 1, 4) == 4);
    assert(findLeftMax(seg, 3, 2) == 2);
    seg.ch(0, &Node::ch, 100);
    // [100, 2, 3, 4, 5]
    assert(getMin(seg, 0, 3) == 2);
    assert(getMax(seg, 0, 3) == 100);
    assert(findRightMin(seg, 0, 3) == 2);
    assert(findLeftMin(seg, 5, 1) == -1);
    assert(findRightMax(seg, 0, 3) == 1);
    assert(findLeftMax(seg, 5, 1) == 4);
    seg.change(3, 10);
    // [100, 2, 3, 10, 5]
    assert(getMin(seg, 3, 5) == 5);
    assert(getMax(seg, 3, 5) == 10);
    assert(findRightMin(seg, 2, 1) == seg.n + 1);
    assert(findLeftMin(seg, 4, INF) == 4);
    assert(findRightMax(seg, 2, 1) == 3);
    assert(findLeftMax(seg, 3, -INF) == 3);
  }
  // large
  {
    constexpr int NUM_CASES = 1000;
    constexpr int MIN_N = 1;
    constexpr int MAX_N = 100;
    constexpr int Q = 1000;
    constexpr long long MIN_VAL = -1000000000;
    constexpr long long MAX_VAL = 1000000000;
    for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
      const int N = MIN_N + xrand() % (MAX_N - MIN_N + 1);
      vector<long long> as(N);
      for (int i = 0; i < N; ++i) {
        as[i] = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
      }
      // printf("as =");
      // for (int i = 0; i < N; ++i) printf(" %lld", as[i]);
      // puts("");
      SegmentTreePoint<Node> seg(as);
      for (int q = 0; q < Q; ++q) {
        switch (xrand() % 4) {
          case 0: {
            const int i = xrand() % N;
            const long long b = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            // printf("0 %d %lld\n", i, b);
            as[i] = b;
            seg.ch(i, &Node::ch, b);
          } break;
          case 1: {
            int l, r;
            for (; ; ) {
              l = xrand() % (N + 1);
              r = xrand() % (N + 1);
              if (l <= r) {
                break;
              }
            }
            long long expectedMin = INF, expectedMax = -INF;
            for (int i = l; i < r; ++i) if (expectedMin > as[i]) expectedMin = as[i];
            for (int i = l; i < r; ++i) if (expectedMax < as[i]) expectedMax = as[i];
            const long long actualMin = getMin(seg, l, r);
            const long long actualMax = getMax(seg, l, r);
            // printf("1 %d %d: %lld %lld %lld %lld\n", l, r, expectedMin, expectedMax, actualMin, actualMax);
            assert(expectedMin == actualMin);
            assert(expectedMax == actualMax);
          } break;
          case 2: {
            const int l = xrand() % (N + 1);
            const long long b = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            int expectedMin = seg.n + 1, expectedMax = seg.n + 1;
            for (int i = l; i < N; ++i) if (as[i] <= b) { expectedMin = i + 1; break; }
            for (int i = l; i < N; ++i) if (as[i] >= b) { expectedMax = i + 1; break; }
            const int actualMin = findRightMin(seg, l, b);
            const int actualMax = findRightMax(seg, l, b);
            // printf("2 %d %lld: %d %d %d %d\n", l, b, expectedMin, expectedMax, actualMin, actualMax);
            assert(expectedMin == actualMin);
            assert(expectedMax == actualMax);
          } break;
          case 3: {
            const int r = xrand() % (N + 1);
            const long long b = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            int expectedMin = -1, expectedMax = -1;
            for (int i = r; --i >= 0; ) if (as[i] <= b) { expectedMin = i; break; }
            for (int i = r; --i >= 0; ) if (as[i] >= b) { expectedMax = i; break; }
            const int actualMin = findLeftMin(seg, r, b);
            const int actualMax = findLeftMax(seg, r, b);
            // printf("3 %d %lld: %d %d %d %d\n", r, b, expectedMin, expectedMax, actualMin, actualMax);
            assert(expectedMin == actualMin);
            assert(expectedMax == actualMax);
          } break;
          default: assert(false);
        }
      }
    }
  }
}
}  // namespace point_change_range_min_range_max

////////////////////////////////////////////////////////////////////////////////

namespace yosupo_point_set_range_composite {
// https://judge.yosupo.jp/problem/point_set_range_composite
//   update point  a[i] <- b
//   get  prod a[l, r)

constexpr long long MO = 998244353;

// x -> x a + b
struct Node {
  long long a, b;
  Node() : a(1), b(0) {}
  Node(long long a_, long long b_) : a(a_), b(b_) {}
  void pull(const Node &l, const Node &r) {
    a = (l.a * r.a) % MO;
    b = (l.b * r.a + r.b) % MO;
  }
  void ch(long long a_, long long b_) {
    a = a_;
    b = b_;
  }
  long long eval(long long x) const {
    return (x * a + b) % MO;
  }
};

void unittest() {
  {
    SegmentTreePoint<Node> seg(vector<Node>{
        Node{1, 2}, Node{3, 4}, Node{5, 6}, Node{7, 8}, Node{9, 10}});
    assert(seg.get(0, 5).eval(11) == 14005);
    assert(seg.get(2, 4).eval(12) == 470);
    seg.ch(1, &Node::ch, 13, 14);
    assert(seg.get(0, 4).eval(15) == 8275);
    assert(seg.get(2, 5).eval(16) == 5500);
  }
}

void solve() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    vector<Node> F(N);
    for (int i = 0; i < N; ++i) {
      scanf("%lld%lld", &F[i].a, &F[i].b);
    }
    SegmentTreePoint<Node> seg(F);
    for (int q = 0; q < Q; ++q) {
      int typ;
      scanf("%d", &typ);
      switch (typ) {
        case 0: {
          int i;
          long long a, b;
          scanf("%d%lld%lld", &i, &a, &b);
          seg.ch(i, &Node::ch, a, b);
        } break;
        case 1: {
          int l, r;
          long long x;
          scanf("%d%d%lld", &l, &r, &x);
          const Node res = seg.get(l, r);
          const long long ans = res.eval(x);
          printf("%lld\n", ans);
        } break;
        default: assert(false);
      }
    }
  }
}
}  // namespace yosupo_point_set_range_composite

////////////////////////////////////////////////////////////////////////////////

void unittests() {
  point_change_range_min_range_max::unittest(); cerr << "PASSED point_change_range_min_range_max::unittest" << endl;
  yosupo_point_set_range_composite::unittest(); cerr << "PASSED yosupo_point_set_range_composite::unittest" << endl;
}

int main() {
  unittests();
  // yosupo_point_set_range_composite::solve();
  return 0;
}
