#include <assert.h>
#include <vector>

using std::vector;

// T: monoid representing information of an interval.
//   T()  should return the identity.
//   T(S s)  should represent a single element of the array.
//   T::push(T &l, T &r)  should push the lazy update.
//   T::pull(const T &l, const T &r)  should pull two intervals.
template <class T> struct SegmentTreeRec {
  int logN, n;
  vector<T> ts;
  SegmentTreeRec() {}
  explicit SegmentTreeRec(int n_) {
    for (logN = 0, n = 1; n < n_; ++logN, n <<= 1) {}
    ts.resize(n << 1);
  }
  template <class S> explicit SegmentTreeRec(const vector<S> &ss) {
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

  inline void push(int u) {
    ts[u].push(ts[u << 1], ts[u << 1 | 1]);
  }
  inline void pull(int u) {
    ts[u].pull(ts[u << 1], ts[u << 1 | 1]);
  }

  // Applies T::f(args...) to [a, b).
  //   f should return true on success. It must succeed for a single element.
  template <class F, class... Args>
  void ch(int a, int b, F f, Args &&... args) {
    assert(0 <= a); assert(a <= b); assert(b <= n);
    if (a == b) return;
    a += n; b += n;
    for (int h = logN; h; --h) {
      const int aa = a >> h, bb = b >> h;
      if (aa == bb) {
        if ((aa << h) != a || (bb << h) != b) push(aa);
      } else {
        if ((aa << h) != a) push(aa);
        if ((bb << h) != b) push(bb);
      }
    }
    for (int aa = a, bb = b; aa < bb; aa >>= 1, bb >>= 1) {
      if (aa & 1) chRec(aa++, f, args...);
      if (bb & 1) chRec(--bb, f, args...);
    }
    for (int h = 1; h <= logN; ++h) {
      const int aa = a >> h, bb = b >> h;
      if (aa == bb) {
        if ((aa << h) != a || (bb << h) != b) pull(aa);
      } else {
        if ((aa << h) != a) pull(aa);
        if ((bb << h) != b) pull(bb);
      }
    }
  }
  template <class F, class... Args>
  void chRec(int u, F f, Args &&... args) {
    const int u0 = u;
    for (; ; ) {
      if ((ts[u].*f)(args...)) {
        for (; u0 < u && (u & 1); pull(u >>= 1)) {}
        if (u0 == u) return;
        ++u;
      } else {
        push(u);
        u <<= 1;
      }
    }
  }

  // Calculates the product for [a, b).
  T get(int a, int b) {
    assert(0 <= a); assert(a <= b); assert(b <= n);
    if (a == b) return T();
    a += n; b += n;
    for (int h = logN; h; --h) {
      const int aa = a >> h, bb = b >> h;
      if (aa == bb) {
        if ((aa << h) != a || (bb << h) != b) push(aa);
      } else {
        if ((aa << h) != a) push(aa);
        if ((bb << h) != b) push(bb);
      }
    }
    T prodL, prodR, t;
    for (int aa = a, bb = b; aa < bb; aa >>= 1, bb >>= 1) {
      if (aa & 1) { t.pull(prodL, ts[aa++]); prodL = t; }
      if (bb & 1) { t.pull(ts[--bb], prodR); prodR = t; }
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
    a += n; b += n;
    for (int h = logN; h; --h) {
      const int aa = a >> h, bb = b >> h;
      if (aa == bb) {
        if ((aa << h) != a || (bb << h) != b) push(aa);
      } else {
        if ((aa << h) != a) push(aa);
        if ((bb << h) != b) push(bb);
      }
    }
    auto prodL = e(), prodR = e();
    for (int aa = a, bb = b; aa < bb; aa >>= 1, bb >>= 1) {
      if (aa & 1) prodL = op(prodL, (ts[aa++].*f)(args...));
      if (bb & 1) prodR = op((ts[--bb].*f)(args...), prodR);
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
    for (int h = logN; h; --h) push(a >> h);
    for (; ; a >>= 1) if (a & 1) {
      if ((ts[a].*f)(args...)) {
        for (; a < n; ) {
          push(a);
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
    for (int h = logN; h; --h) push((b - 1) >> h);
    for (; ; b >>= 1) if ((b & 1) || b == 2) {
      if ((ts[b - 1].*f)(args...)) {
        for (; b <= n; ) {
          push(b - 1);
          if (!(ts[(b <<= 1) - 1].*f)(args...)) --b;
        }
        return b - n - 1;
      }
      --b;
      if (!(b & (b - 1))) return -1;
    }
  }
};

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

namespace hdu_5306 {

// https://acm.hdu.edu.cn/showproblem.php?pid=5306
//   update range  a[i] <- min(a[i], t)
//   get  max a[l, r)
//   get  sum a[l, r)
// O((N + Q) log N)

using std::max;

constexpr long long INF = 1001001001001001001LL;

struct Node {
  long long mx, mx2, mxNum, sz, sum;
  // change mx to lz
  long long lz;
  Node() : mx(-INF), mx2(-INF), mxNum(0), sz(0), sum(0), lz(INF) {}
  Node(long long val) : mx(val), mx2(-INF), mxNum(1), sz(1), sum(val), lz(INF) {}
  void push(Node &l, Node &r) {
    if (lz != INF) {
      if (!l.chmin(lz)) assert(false);
      if (!r.chmin(lz)) assert(false);
      lz = INF;
    }
  }
  void pull(const Node &l, const Node &r) {
    mx = max(l.mx, r.mx);
    mx2 = max((l.mx == mx) ? l.mx2 : l.mx, (r.mx == mx) ? r.mx2 : r.mx);
    mxNum = ((l.mx == mx) ? l.mxNum : 0) + ((r.mx == mx) ? r.mxNum : 0);
    sz = l.sz + r.sz;
    sum = l.sum + r.sum;
  }
  bool chmin(long long val) {
    if (val <= mx2) {
      return false;
    } else if (val < mx) {
      sum -= mxNum * (mx - val);
      mx = val;
      lz = val;
      return true;
    } else {
      return true;
    }
  }
  long long getMax() const {
    return mx;
  }
  long long getSum() const {
    return sum;
  }
};

long long getMax(SegmentTreeRec<Node> &seg, int a, int b) {
  return seg.get(a, b,
                 [&](long long l, long long r) -> long long { return max(l, r); },
                 [&]() -> long long { return -INF; },
                 &Node::getMax);
}
long long getSum(SegmentTreeRec<Node> &seg, int a, int b) {
  return seg.get(a, b,
                 [&](long long l, long long r) -> long long { return l + r; },
                 [&]() -> long long { return 0LL; },
                 &Node::getSum);
}

void unittest() {
  {
    SegmentTreeRec<Node> seg(vector<long long>{1, 2, 3, 4, 5});
    assert(getMax(seg, 0, 5) == 5);
    assert(getSum(seg, 0, 5) == 15);
    seg.ch(2, 5, &Node::chmin, 3);
    assert(getMax(seg, 0, 5) == 3);
    assert(getSum(seg, 0, 5) == 12);
  }
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
      SegmentTreeRec<Node> seg(as);
      for (int q = 0; q < Q; ++q) {
        int l, r;
        for (; ; ) {
          l = xrand() % N;
          r = 1 + xrand() % N;
          if (l < r) {
            break;
          }
        }
        switch (xrand() % 3) {
          case 0: {
            const long long t = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            // printf("0 %d %d %lld\n", l, r, t);
            for (int i = l; i < r; ++i) if (as[i] > t) as[i] = t;
            seg.ch(l, r, &Node::chmin, t);
          } break;
          case 1: {
            long long expected = -INF;
            for (int i = l; i < r; ++i) if (expected < as[i]) expected = as[i];
            const long long actual = getMax(seg, l, r);
            // printf("1 %d %d: %lld %lld\n", l, r, expected, actual);
            assert(expected == actual);
          } break;
          case 2: {
            long long expected = 0;
            for (int i = l; i < r; ++i) expected += as[i];
            const long long actual = getSum(seg, l, r);
            // printf("2 %d %d: %lld %lld\n", l, r, expected, actual);
            assert(expected == actual);
          } break;
          default: assert(false);
        }
      }
    }
  }
}

void solve() {
  for (int numCases; ~scanf("%d", &numCases); ) for (; numCases--; ) {
    int N, Q;
    scanf("%d%d", &N, &Q);
    vector<long long> A(N);
    for (int i = 0; i < N; ++i) {
      scanf("%lld", &A[i]);
    }
    SegmentTreeRec<Node> seg(A);
    for (int q = 0; q < Q; ++q) {
      int typ, l, r;
      scanf("%d%d%d", &typ, &l, &r);
      --l;
      switch (typ) {
        case 0: {
          long long t;
          scanf("%lld", &t);
          seg.ch(l, r, &Node::chmin, t);
        } break;
        case 1: {
          const long long res = getMax(seg, l, r);
          printf("%lld\n", res);
        } break;
        case 2: {
          const long long res = getSum(seg, l, r);
          printf("%lld\n", res);
        } break;
        default: assert(false);
      }
    }
  }
}

}  // namespace hdu_5306

////////////////////////////////////////////////////////////////////////////////

namespace yosupo_range_chmin_chmax_add_range_sum {

// https://judge.yosupo.jp/problem/range_chmin_chmax_add_range_sum
//   update range  a[i] <- min(a[i], b)
//   update range  a[i] <- max(a[i], b)
//   update range  a[i] <- a[i] + b
//   get  sum a[l, r)
// O((N + Q) (log N)^2)

using std::max;
using std::min;

constexpr long long INF = 1001001001001001001LL;

// x -> min(max(x + a, b), c)
// invariant: b <= c
struct Func {
  long long a, b, c;
  Func() : a(0), b(-INF), c(+INF) {}
  Func(long long a_, long long b_, long long c_) : a(a_), b(b_), c(c_) {}
  void add(long long val) {
    a += val;
    b += val;
    c += val;
  }
  void chmin(long long val) {
    if (b > val) b = val;
    if (c > val) c = val;
  }
  void chmax(long long val) {
    if (b < val) b = val;
    if (c < val) c = val;
  }
};

struct Node {
  long long mn, mn2, mx, mx2, sum;
  long long mnNum, mxNum, sz;
  Func lz;
  Node() : mn(+INF), mn2(+INF), mx(-INF), mx2(-INF), sum(0), mnNum(0), mxNum(0), sz(0), lz() {}
  Node(long long val) : mn(val), mn2(+INF), mx(val), mx2(-INF), sum(val), mnNum(1), mxNum(1), sz(1), lz() {}
  void push(Node &l, Node &r) {
    if (!l.ch(lz)) assert(false);
    if (!r.ch(lz)) assert(false);
    lz = Func();
  }
  void pull(const Node &l, const Node &r) {
    mn = min(l.mn, r.mn);
    mn2 = min((l.mn == mn) ? l.mn2 : l.mn, (r.mn == mn) ? r.mn2 : r.mn);
    mnNum = ((l.mn == mn) ? l.mnNum : 0) + ((r.mn == mn) ? r.mnNum : 0);
    mx = max(l.mx, r.mx);
    mx2 = max((l.mx == mx) ? l.mx2 : l.mx, (r.mx == mx) ? r.mx2 : r.mx);
    mxNum = ((l.mx == mx) ? l.mxNum : 0) + ((r.mx == mx) ? r.mxNum : 0);
    sum = l.sum + r.sum;
    sz = l.sz + r.sz;
  }
  bool ch(const Func &f) {
    if (!add(f.a)) return false;
    if (!chmax(f.b)) return false;
    if (!chmin(f.c)) return false;
    return true;
  }
  bool chmin(long long val) {
    if (val < +INF) {
      if (val <= mx2) {
        return false;
      } else if (val < mx) {
        if (mn == mx) mn = val;
        if (mn2 == mx) mn2 = val;
        sum -= mxNum * (mx - val);
        mx = val;
        lz.chmin(val);
      }
    }
    return true;
  }
  bool chmax(long long val) {
    if (val > -INF) {
      if (val >= mn2) {
        return false;
      } else if (val > mn) {
        if (mx == mn) mx = val;
        if (mx2 == mn) mx2 = val;
        sum += mnNum * (val - mn);
        mn = val;
        lz.chmax(val);
      }
    }
    return true;
  }
  bool add(long long val) {
    if (val != 0) {
      mn += val;
      if (mn2 < +INF) mn2 += val;
      mx += val;
      if (mx2 > -INF) mx2 += val;
      sum += sz * val;
      lz.add(val);
    }
    return true;
  }
  long long getSum() const {
    return sum;
  }
  bool accSum(long long &acc, long long tar) const {
    if (acc + sum >= tar) return true;
    acc += sum;
    return false;
  }
};

long long getSum(SegmentTreeRec<Node> &seg, int a, int b) {
  return seg.get(a, b,
                 [&](long long l, long long r) -> long long { return l + r; },
                 [&]() -> long long { return 0LL; },
                 &Node::getSum);
}

// (sum of [a, b)) >= target
int findRight(SegmentTreeRec<Node> &seg, int a, long long tar) {
  long long acc = 0;
  return seg.findRight(a, &Node::accSum, acc, tar);
}
int findLeft(SegmentTreeRec<Node> &seg, int b, long long tar) {
  long long acc = 0;
  return seg.findLeft(b, &Node::accSum, acc, tar);
}

void unittest() {
  // Func
  {
    constexpr long long MIN_VAL = -10;
    constexpr long long MAX_VAL = 10;
    for (long long a = MIN_VAL; a <= MAX_VAL; ++a) for (long long b = MIN_VAL; b <= MAX_VAL; ++b) for (long long c = MIN_VAL; c <= MAX_VAL; ++c) {
      if (b <= c) {
        for (long long d = MIN_VAL; d <= MAX_VAL; ++d) {
          for (long long x = MIN_VAL; x <= MAX_VAL; ++x) {
            {
              Func f(a, b, c);
              f.add(d);
              assert(f.b <= f.c);
              assert(min(max(x + a, b), c) + d == min(max(x + f.a, f.b), f.c));
            }
            {
              Func f(a, b, c);
              f.chmin(d);
              assert(f.b <= f.c);
              assert(min(min(max(x + a, b), c), d) == min(max(x + f.a, f.b), f.c));
            }
            {
              Func f(a, b, c);
              f.chmax(d);
              assert(f.b <= f.c);
              assert(max(min(max(x + a, b), c), d) == min(max(x + f.a, f.b), f.c));
            }
          }
        }
      }
    }
  }
  // small
  {
    SegmentTreeRec<Node> seg(vector<long long>{1, 2, 3, 4, 5});
    // [1, 2, 3, 4, 5]
    assert(getSum(seg, 0, 5) == 15);
    assert(seg.get(0, 5).sum == 15);
    assert(findRight(seg, 1, 4) == 3);
    assert(findLeft(seg, 3, 5) == 1);
    seg.ch(2, 4, &Node::add, 100);
    // [1, 2, 103, 104, 5]
    assert(seg.get(0, 3).mn == 1);
    assert(seg.get(0, 3).mx == 103);
    assert(getSum(seg, 0, 3) == 106);
    assert(findRight(seg, 0, 210) == 4);
    assert(findLeft(seg, 5, 216) == -1);
    seg.ch(1, 3, &Node::chmin, 10);
    // [1, 2, 10, 104, 5]
    assert(getSum(seg, 2, 5) == 119);
    assert(seg.get(2, 5).mn2 == 10);
    assert(seg.get(2, 5).mx2 == 10);
    assert(findRight(seg, 2, 120) == seg.n + 1);
    assert(findLeft(seg, 4, 117) == 0);
    seg.ch(2, 5, &Node::chmax, 20);
    // [1, 2, 20, 104, 5]
    assert(seg.get(0, 5).sum == 147);
    assert(getSum(seg, 0, 5) == 147);
    assert(findRight(seg, 3, 100) == 4);
    assert(findLeft(seg, 2, 2) == 1);
  }
  // large without findRight, findLeft
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
      SegmentTreeRec<Node> seg(as);
      for (int q = 0; q < Q; ++q) {
        int l, r;
        for (; ; ) {
          l = xrand() % N;
          r = 1 + xrand() % N;
          if (l < r) {
            break;
          }
        }
        switch (xrand() % 4) {
          case 0: {
            const long long b = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            // printf("0 %d %d %lld\n", l, r, b);
            for (int i = l; i < r; ++i) if (as[i] > b) as[i] = b;
            seg.ch(l, r, &Node::chmin, b);
          } break;
          case 1: {
            const long long b = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            // printf("1 %d %d %lld\n", l, r, b);
            for (int i = l; i < r; ++i) if (as[i] < b) as[i] = b;
            seg.ch(l, r, &Node::chmax, b);
          } break;
          case 2: {
            const long long b = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            // printf("2 %d %d %lld\n", l, r, b);
            for (int i = l; i < r; ++i) as[i] += b;
            seg.ch(l, r, &Node::add, b);
          } break;
          case 3: {
            long long expected = 0;
            for (int i = l; i < r; ++i) expected += as[i];
            const long long actual = getSum(seg, l, r);
            // printf("3 %d %d: %lld %lld\n", l, r, expected, actual);
            assert(expected == actual);
          } break;
          default: assert(false);
        }
      }
    }
  }
  // large with findRight, findLeft
  {
    constexpr int NUM_CASES = 1000;
    constexpr int MIN_N = 1;
    constexpr int MAX_N = 100;
    constexpr int Q = 1000;
    constexpr long long MIN_VAL = 0;
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
      SegmentTreeRec<Node> seg(as);
      for (int q = 0; q < Q; ++q) {
        int l, r;
        for (; ; ) {
          l = xrand() % (N + 1);
          r = xrand() % (N + 1);
          if (l <= r) {
            break;
          }
        }
        switch (xrand() % 6) {
          case 0: {
            const long long b = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            // printf("0 %d %d %lld\n", l, r, b);
            for (int i = l; i < r; ++i) if (as[i] > b) as[i] = b;
            seg.ch(l, r, &Node::chmin, b);
          } break;
          case 1: {
            const long long b = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            // printf("1 %d %d %lld\n", l, r, b);
            for (int i = l; i < r; ++i) if (as[i] < b) as[i] = b;
            seg.ch(l, r, &Node::chmax, b);
          } break;
          case 2: {
            const long long b = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            // printf("2 %d %d %lld\n", l, r, b);
            for (int i = l; i < r; ++i) as[i] += b;
            seg.ch(l, r, &Node::add, b);
          } break;
          case 3: {
            long long expected = 0;
            for (int i = l; i < r; ++i) expected += as[i];
            const long long actual = getSum(seg, l, r);
            // printf("3 %d %d: %lld %lld\n", l, r, expected, actual);
            assert(expected == actual);
          } break;
          case 4: {
            if (l == r || as[r - 1] > 0) {
              long long b = 0;
              for (int i = l; i < r; ++i) b += as[i];
              if (l != r) b -= xrand() % as[r - 1];
              const int actual = findRight(seg, l, b);
              // printf("4 %d %lld: %d %d\n", l, b, r, actual);
              assert(r == actual);
            } else {
              long long b = 0;
              for (int i = l; i < N; ++i) b += as[i];
              b += 1 + xrand() % MAX_VAL;
              const int actual = findRight(seg, l, b);
              // printf("4 %d %lld: %d %d\n", l, b, seg.n + 1, actual);
              assert(seg.n + 1 == actual);
            }
          } break;
          case 5: {
            if (l == r || as[l] > 0) {
              long long b = 0;
              for (int i = r; --i >= l; ) b += as[i];
              if (l != r) b -= xrand() % as[l];
              const int actual = findLeft(seg, r, b);
              // printf("5 %d %lld: %d %d\n", r, b, l, actual);
              assert(l == actual);
            } else {
              long long b = 0;
              for (int i = r; --i >= 0; ) b += as[i];
              b += 1 + xrand() % MAX_VAL;
              const int actual = findLeft(seg, r, b);
              // printf("5 %d %lld: %d %d\n", l, b, -1, actual);
              assert(-1 == actual);
            }
          } break;
          default: assert(false);
        }
      }
    }
  }
}

void solve() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    vector<long long> A(N);
    for (int i = 0; i < N; ++i) {
      scanf("%lld", &A[i]);
    }
    SegmentTreeRec<Node> seg(A);
    for (int q = 0; q < Q; ++q) {
      int typ, l, r;
      scanf("%d%d%d", &typ, &l, &r);
      switch (typ) {
        case 0: {
          long long b;
          scanf("%lld", &b);
          seg.ch(l, r, &Node::chmin, b);
        } break;
        case 1: {
          long long b;
          scanf("%lld", &b);
          seg.ch(l, r, &Node::chmax, b);
        } break;
        case 2: {
          long long b;
          scanf("%lld", &b);
          seg.ch(l, r, &Node::add, b);
        } break;
        case 3: {
          const long long res = getSum(seg, l, r);
          printf("%lld\n", res);
        } break;
        default: assert(false);
      }
    }
  }
}

}  // namespace yosupo_range_chmin_chmax_add_range_sum

////////////////////////////////////////////////////////////////////////////////

namespace yukicoder_880 {

// https://yukicoder.me/problems/no/880
//   update range  a[i] <- x
//   update range  a[i] <- gcd(a[i], x)
//   get  max a[l, r)
//   get  sum a[l, r)
// O((N + Q) log N (log max (a[i], x))^2)

using std::max;
using std::min;
using std::swap;

constexpr long long INF = 1001001001001001001LL;

long long gcd(long long a, long long b) {
  if (a < 0) a = -a;
  if (b < 0) b = -b;
  if (a == 0) return b;
  if (b == 0) return a;
  const int s = __builtin_ctzll(a | b);
  a >>= __builtin_ctzll(a);
  do {
    b >>= __builtin_ctzll(b);
    if (a > b) swap(a, b);
    b -= a;
  } while (b);
  return a << s;
}

struct Node {
  long long lcm, mx, sz, sum;
  // assign lz
  long long lz;
  Node() : lcm(1), mx(0), sz(0), sum(0), lz(-1) {}
  Node(long long val) : lcm(val), mx(val), sz(1), sum(val), lz(-1) {}
  void push(Node &l, Node &r) {
    if (lz != -1) {
      if (!l.assign(lz)) assert(false);
      if (!r.assign(lz)) assert(false);
      lz = -1;
    }
  }
  void pull(const Node &l, const Node &r) {
    lcm = (l.lcm <= INF / r.lcm) ? min(l.lcm / gcd(l.lcm, r.lcm) * r.lcm, INF) : INF;
    mx = max(l.mx, r.mx);
    sz = l.sz + r.sz;
    sum = l.sum + r.sum;
  }
  bool assign(long long val) {
    lcm = val;
    mx = val;
    sum = sz * val;
    lz = val;
    return true;
  }
  bool chgcd(long long val) {
    if (val % lcm == 0) {
      return true;
    } else if (sz * mx == sum) {
      return assign(gcd(lcm, val));
    } else {
      return false;
    }
  }
  long long getMax() const {
    return mx;
  }
  long long getSum() const {
    return sum;
  }
};

long long getMax(SegmentTreeRec<Node> &seg, int a, int b) {
  return seg.get(a, b,
                 [&](long long l, long long r) -> long long { return max(l, r); },
                 [&]() -> long long { return 0LL; },
                 &Node::getMax);
}
long long getSum(SegmentTreeRec<Node> &seg, int a, int b) {
  return seg.get(a, b,
                 [&](long long l, long long r) -> long long { return l + r; },
                 [&]() -> long long { return 0LL; },
                 &Node::getSum);
}

void unittest() {
  {
    SegmentTreeRec<Node> seg(vector<long long>{1, 6, 8, 7, 3});
    assert(getMax(seg, 0, 5) == 8);
    assert(getSum(seg, 0, 5) == 25);
    seg.ch(0, 5, &Node::chgcd, 6);
    assert(getMax(seg, 0, 5) == 6);
    assert(getSum(seg, 1, 4) == 9);
    seg.ch(0, 5, &Node::assign, 10);
    assert(getMax(seg, 0, 4) == 10);
    assert(getSum(seg, 2, 5) == 30);
    seg.ch(2, 4, &Node::chgcd, 3);
    assert(getMax(seg, 1, 3) == 10);
    assert(getSum(seg, 3, 5) == 11);
  }
  {
    constexpr int NUM_CASES = 1000;
    constexpr int MIN_N = 1;
    constexpr int MAX_N = 100;
    constexpr int Q = 1000;
    constexpr long long MIN_VAL = 1;
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
      SegmentTreeRec<Node> seg(as);
      for (int q = 0; q < Q; ++q) {
        int l, r;
        for (; ; ) {
          l = xrand() % N;
          r = 1 + xrand() % N;
          if (l < r) {
            break;
          }
        }
        switch (1 + xrand() % 4) {
          case 1: {
            const long long x = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            // printf("1 %d %d %lld\n", l, r, x);
            for (int i = l; i < r; ++i) as[i] = x;
            seg.ch(l, r, &Node::assign, x);
          } break;
          case 2: {
            const long long x = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            // printf("2 %d %d %lld\n", l, r, x);
            for (int i = l; i < r; ++i) as[i] = gcd(as[i], x);
            seg.ch(l, r, &Node::chgcd, x);
          } break;
          case 3: {
            long long expected = -INF;
            for (int i = l; i < r; ++i) if (expected < as[i]) expected = as[i];
            const long long actual = getMax(seg, l, r);
            // printf("3 %d %d: %lld %lld\n", l, r, expected, actual);
            assert(expected == actual);
          } break;
          case 4: {
            long long expected = 0;
            for (int i = l; i < r; ++i) expected += as[i];
            const long long actual = getSum(seg, l, r);
            // printf("4 %d %d: %lld %lld\n", l, r, expected, actual);
            assert(expected == actual);
          } break;
          default: assert(false);
        }
      }
    }
  }
}

void solve() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    vector<long long> A(N);
    for (int i = 0; i < N; ++i) {
      scanf("%lld", &A[i]);
    }
    SegmentTreeRec<Node> seg(A);
    for (int q = 0; q < Q; ++q) {
      int typ, l, r;
      scanf("%d%d%d", &typ, &l, &r);
      --l;
      switch (typ) {
        case 1: {
          long long x;
          scanf("%lld", &x);
          seg.ch(l, r, &Node::assign, x);
        } break;
        case 2: {
          long long x;
          scanf("%lld", &x);
          seg.ch(l, r, &Node::chgcd, x);
        } break;
        case 3: {
          const long long res = getMax(seg, l, r);
          printf("%lld\n", res);
        } break;
        case 4: {
          const long long res = getSum(seg, l, r);
          printf("%lld\n", res);
        } break;
        default: assert(false);
      }
    }
  }
}

}  // namespace yukicoder_880

////////////////////////////////////////////////////////////////////////////////

namespace uoj_671_slow {

// https://uoj.ac/problem/671
//   update range  a[i] <- floor(a[i] / v)
//   update range  a[i] <- a[i] & v
//   get  sum a[l, r)
// O(N w^2 + Q log N)

using std::max;

using u128 = unsigned __int128;

u128 in() {
  static char buf[40];
  scanf("%s", buf);
  u128 x = 0;
  for (char *p = buf; *p; ++p) x = x << 4 | ((*p >= 'a') ? (10 + (*p - 'a')) : (*p - '0'));
  return x;
}
void out(u128 x) {
  if (x >> 4) out(x >> 4);
  x &= 15;
  putchar((x >= 10) ? ('a' + (x - 10)) : ('0' + x));
}

struct Node {
  u128 sum, bor;
  int sz;
  Node() : sum(0), bor(0), sz(0) {}
  Node(u128 val) : sum(val), bor(val), sz(1) {}
  void push(Node &, Node &) {}
  void pull(const Node &l, const Node &r) {
    sum = l.sum + r.sum;
    bor = l.bor | r.bor;
    sz = l.sz + r.sz;
  }
  bool chdiv(u128 val) {
    if (bor == 0 || val == 1) {
      return true;
    } else if (sz == 1) {
      sum = bor = sum / val;
      return true;
    } else {
      return false;
    }
  }
  bool chand(u128 val) {
    if (!(bor & ~val)) {
      return true;
    } else if (sz == 1) {
      sum = bor = sum & val;
      return true;
    } else {
      return false;
    }
  }
  u128 getSum() const {
    return sum;
  }
};

u128 getSum(SegmentTreeRec<Node> &seg, int a, int b) {
  return seg.get(a, b,
                 [&](u128 l, u128 r) -> u128 { return l + r; },
                 [&]() -> u128 { return (u128)0; },
                 &Node::getSum);
}

void unittest() {
  {
    SegmentTreeRec<Node> seg(vector<u128>{1, 9, 1, 9, 1});
    assert(getSum(seg, 1, 3) == 10);
    seg.ch(0, 3, &Node::chand, 5);
    assert(getSum(seg, 0, 5) == 13);
    seg.ch(0, 5, &Node::chdiv, 3);
    assert(getSum(seg, 0, 5) == 3);
  }
  {
    constexpr int NUM_CASES = 1000;
    constexpr int MIN_N = 1;
    constexpr int MAX_N = 100;
    constexpr int Q = 1000;
    constexpr u128 MIN_VAL = 1;
    constexpr u128 MAX_VAL = 1000000000;
    for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
      const int N = MIN_N + xrand() % (MAX_N - MIN_N + 1);
      vector<u128> as(N);
      for (int i = 0; i < N; ++i) {
        as[i] = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
      }
      SegmentTreeRec<Node> seg(as);
      for (int q = 0; q < Q; ++q) {
        int l, r;
        for (; ; ) {
          l = xrand() % N;
          r = 1 + xrand() % N;
          if (l < r) {
            break;
          }
        }
        switch (1 + xrand() % 3) {
          case 1: {
            const u128 v = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            for (int i = l; i < r; ++i) as[i] /= v;
            seg.ch(l, r, &Node::chdiv, v);
          } break;
          case 2: {
            const u128 v = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            for (int i = l; i < r; ++i) as[i] &= v;
            seg.ch(l, r, &Node::chand, v);
          } break;
          case 3: {
            u128 expected = 0;
            for (int i = l; i < r; ++i) expected += as[i];
            const u128 actual = getSum(seg, l, r);
            assert(expected == actual);
          } break;
          default: assert(false);
        }
      }
    }
  }
}

void solve() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    vector<u128> A(N);
    for (int i = 0; i < N; ++i) {
      A[i] = in();
    }
    SegmentTreeRec<Node> seg(A);
    for (int q = 0; q < Q; ++q) {
      int typ, l, r;
      scanf("%d%d%d", &typ, &l, &r);
      --l;
      switch (typ) {
        case 1: {
          const u128 v = in();
          seg.ch(l, r, &Node::chdiv, v);
        } break;
        case 2: {
          const u128 v = in();
          seg.ch(l, r, &Node::chand, v);
        } break;
        case 3: {
          const u128 res = getSum(seg, l, r);
          out(res);
          putchar('\n');
        } break;
        default: assert(false);
      }
    }
  }
}

}  // namespace uoj_671_slow

////////////////////////////////////////////////////////////////////////////////

namespace uoj_671 {

// https://uoj.ac/problem/671
//   update range  a[i] <- floor(a[i] / v)
//   update range  a[i] <- a[i] & v
//   get  sum a[l, r)
// O(N w + Q (log N)^2)

using std::max;

using u128 = unsigned __int128;

u128 in() {
  static char buf[40];
  scanf("%s", buf);
  u128 x = 0;
  for (char *p = buf; *p; ++p) x = x << 4 | ((*p >= 'a') ? (10 + (*p - 'a')) : (*p - '0'));
  return x;
}
void out(u128 x) {
  if (x >> 4) out(x >> 4);
  x &= 15;
  putchar((x >= 10) ? ('a' + (x - 10)) : ('0' + x));
}

// 4 seg.n
u128 pool_[1 << 21], *pool = pool_;

struct Node {
  bool any;
  // cnt[i] for 2^i occurrences of each bit  (0 <= i < len = log_2(sz) + 1)
  int len;
  u128 *cnt;
  // &= lz
  u128 lz;
  Node() : any(0), len(0), cnt(nullptr), lz(~(u128)0) {}
  Node(u128 val) : any(val), lz(~(u128)0) {
    alloc(1);
    cnt[0] = val;
  }
  void alloc(int len_) {
    len = len_;
    cnt = pool;
    pool += len;
  }
  void push(Node &l, Node &r) {
    if (~lz) {
      l.chand(lz);
      r.chand(lz);
      lz = ~(u128)0;
    }
  }
  void pull(const Node &l, const Node &r) {
    if (len == 0) alloc(l.len + 1);
    any = l.any || r.any;
    if (r.len == 0) {
      for (int i = 0; i < len - 1; ++i) cnt[i] = l.cnt[i];
      cnt[len - 1] = 0;
    } else {
      u128 carry = 0;
      for (int i = 0; i < len - 1; ++i) {
        const u128 tmp0 = l.cnt[i] ^ r.cnt[i];
        const u128 tmp1 = l.cnt[i] & r.cnt[i];
        cnt[i] = tmp0 ^ carry;
        carry = tmp1 | (tmp0 & carry);
      }
      cnt[len - 1] = carry;
    }
  }
  bool chdiv(u128 val) {
    if (!any || val == 1) {
      return true;
    } else if (len == 1) {
      cnt[0] /= val;
      any = cnt[0];
      return true;
    } else {
      return false;
    }
  }
  bool chand(u128 val) {
    for (int i = 0; i < len; ++i) {
      cnt[i] &= val;
      any = any || cnt[i];
    }
    lz &= val;
    return true;
  }
  u128 getSum() const {
    u128 sum = 0;
    for (int i = 0; i < len; ++i) {
      sum += cnt[i] << i;
    }
    return sum;
  }
};

u128 getSum(SegmentTreeRec<Node> &seg, int a, int b) {
  return seg.get(a, b,
                 [&](u128 l, u128 r) -> u128 { return l + r; },
                 [&]() -> u128 { return (u128)0; },
                 &Node::getSum);
}

void unittest() {
  {
    pool = pool_;
    SegmentTreeRec<Node> seg(vector<u128>{1, 9, 1, 9, 1});
    assert(getSum(seg, 1, 3) == 10);
    seg.ch(0, 3, &Node::chand, 5);
    assert(getSum(seg, 0, 5) == 13);
    seg.ch(0, 5, &Node::chdiv, 3);
    assert(getSum(seg, 0, 5) == 3);
  }
  {
    constexpr int NUM_CASES = 1000;
    constexpr int MIN_N = 1;
    constexpr int MAX_N = 100;
    constexpr int Q = 1000;
    constexpr u128 MIN_VAL = 1;
    constexpr u128 MAX_VAL = 1000000000;
    for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
      const int N = MIN_N + xrand() % (MAX_N - MIN_N + 1);
      vector<u128> as(N);
      for (int i = 0; i < N; ++i) {
        as[i] = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
      }
      pool = pool_;
      SegmentTreeRec<Node> seg(as);
      for (int q = 0; q < Q; ++q) {
        int l, r;
        for (; ; ) {
          l = xrand() % N;
          r = 1 + xrand() % N;
          if (l < r) {
            break;
          }
        }
        switch (1 + xrand() % 3) {
          case 1: {
            const u128 v = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            for (int i = l; i < r; ++i) as[i] /= v;
            seg.ch(l, r, &Node::chdiv, v);
          } break;
          case 2: {
            const u128 v = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            for (int i = l; i < r; ++i) as[i] &= v;
            seg.ch(l, r, &Node::chand, v);
          } break;
          case 3: {
            u128 expected = 0;
            for (int i = l; i < r; ++i) expected += as[i];
            const u128 actual = getSum(seg, l, r);
            assert(expected == actual);
          } break;
          default: assert(false);
        }
      }
    }
  }
}

void solve() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    vector<u128> A(N);
    for (int i = 0; i < N; ++i) {
      A[i] = in();
    }
    SegmentTreeRec<Node> seg(A);
    for (int q = 0; q < Q; ++q) {
      int typ, l, r;
      scanf("%d%d%d", &typ, &l, &r);
      --l;
      switch (typ) {
        case 1: {
          const u128 v = in();
          seg.ch(l, r, &Node::chdiv, v);
        } break;
        case 2: {
          const u128 v = in();
          seg.ch(l, r, &Node::chand, v);
        } break;
        case 3: {
          const u128 res = getSum(seg, l, r);
          out(res);
          putchar('\n');
        } break;
        default: assert(false);
      }
    }
  }
}

}  // namespace uoj_671

////////////////////////////////////////////////////////////////////////////////

void unittests() {
  hdu_5306::unittest(); cerr << "PASSED hdu_5306::unittest" << endl;
  yosupo_range_chmin_chmax_add_range_sum::unittest(); cerr << "PASSED yosupo_range_chmin_chmax_add_range_sum::unittest" << endl;
  yukicoder_880::unittest(); cerr << "PASSED yukicoder_880::unittest" << endl;
  uoj_671_slow::unittest(); cerr << "PASSED uoj_671_slow::unittest" << endl;
  uoj_671::unittest(); cerr << "PASSED uoj_671::unittest" << endl;
}

int main() {
  unittests();
  // hdu_5306::solve();
  // yosupo_range_chmin_chmax_add_range_sum::solve();
  // yukicoder_880::solve();
  // uoj_671_slow::solve();
  // uoj_671::solve();
  return 0;
}
