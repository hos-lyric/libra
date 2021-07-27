#include <assert.h>
#include <utility>
#include <vector>

using std::declval;
using std::vector;

// T: monoid representing information of an interval.
//   T()  should return the identity.
//   T(S s)  should represent a single element of the array.
//   T::push(T &l, T &r)  should push the lazy update.
//   T::merge(const T &l, const T &r)  should merge two intervals.
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
    for (int u = n; --u; ) merge(u);
  }

  inline void push(int u) {
    ts[u].push(ts[u << 1], ts[u << 1 | 1]);
  }
  inline void merge(int u) {
    ts[u].merge(ts[u << 1], ts[u << 1 | 1]);
  }

  // Applies T::f(args...) to [a, b).
  template <class F, class... Args> void ch(int a, int b, F f, const Args &... args) {
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
        if ((aa << h) != a || (bb << h) != b) merge(aa);
      } else {
        if ((aa << h) != a) merge(aa);
        if ((bb << h) != b) merge(bb);
      }
    }
  }
  template <class F, class... Args> void chRec(int u, F f, const Args &... args) {
    if ((ts[u].*f)(args...)) return;
    push(u);
    chRec(u << 1, f, args...);
    chRec(u << 1 | 1, f, args...);
    merge(u);
  }

  // Calculates T::f(args...) of a monoid type for [a, b).
  //   op(-, -)  should calculate the product.
  //   e()  should return the identity.
  template <class Op, class E, class F, class... Args> decltype((declval<T>().*F())()) get(int a, int b, Op op, E e, F f, const Args &... args) {
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
};

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <algorithm>

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

////////////////////////////////////////////////////////////////////////////////

// https://acm.hdu.edu.cn/showproblem.php?pid=5306
// update range  a[i] <- min(a[i], t)
// get  max a[l, r)
// get  sum a[l, r)

namespace hdu5306 {

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
  void merge(const Node &l, const Node &r) {
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

long long opMax(long long l, long long r) { return max(l, r); }
long long eMax() { return -INF; }
long long opSum(long long l, long long r) { return l + r; }
long long eSum() { return 0; }

void unittest() {
  {
    SegmentTreeRec<Node> seg(vector<long long>{1, 2, 3, 4, 5});
    assert(seg.get(0, 5, &opMax, &eMax, &Node::getMax) == 5);
    assert(seg.get(0, 5, &opSum, &eSum, &Node::getSum) == 15);
    seg.ch(2, 5, &Node::chmin, 3);
    assert(seg.get(0, 5, &opMax, &eMax, &Node::getMax) == 3);
    assert(seg.get(0, 5, &opSum, &eSum, &Node::getSum) == 12);
  }
  {
    constexpr int NUM_CASES = 1000;
    constexpr long long MIN_N = 1;
    constexpr long long MAX_N = 1000;
    constexpr int Q = 1000;
    constexpr long long MIN_VAL = -1000;
    constexpr long long MAX_VAL = 1000;
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
            const long long actual = seg.get(l, r, &opMax, &eMax, &Node::getMax);
            // printf("1 %d %d: %lld %lld\n", l, r, expected, actual);
            assert(expected == actual);
          } break;
          case 2: {
            long long expected = 0;
            for (int i = l; i < r; ++i) expected += as[i];
            const long long actual = seg.get(l, r, &opSum, &eSum, &Node::getSum);
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
          const long long res = seg.get(l, r, &opMax, &eMax, &Node::getMax);
          printf("%lld\n", res);
        } break;
        case 2: {
          const long long res = seg.get(l, r, &opSum, &eSum, &Node::getSum);
          printf("%lld\n", res);
        } break;
        default: assert(false);
      }
    }
  }
}

}  // namespace hdu5306

////////////////////////////////////////////////////////////////////////////////

namespace yukicoder880 {

// https://yukicoder.me/problems/no/880
// update range  a[i] <- x
// update range  a[i] <- gcd(a[i], x)
// get  max a[l, r)
// get  sum a[l, r)

using std::max;
using std::min;
using std::swap;

constexpr long long INF = 1001001001;

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
  void merge(const Node &l, const Node &r) {
    lcm = (l.lcm < INF && r.lcm < INF) ? min(l.lcm / gcd(l.lcm, r.lcm) * r.lcm, INF) : INF;
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

long long opMax(long long l, long long r) { return max(l, r); }
long long eMax() { return 0; }
long long opSum(long long l, long long r) { return l + r; }
long long eSum() { return 0; }

void unittest() {
  {
    SegmentTreeRec<Node> seg(vector<long long>{1, 6, 8, 7, 3});
    assert(seg.get(0, 5, &opMax, &eMax, &Node::getMax) == 8);
    assert(seg.get(0, 5, &opSum, &eSum, &Node::getSum) == 25);
    seg.ch(0, 5, &Node::chgcd, 6);
    assert(seg.get(0, 5, &opMax, &eMax, &Node::getMax) == 6);
    assert(seg.get(1, 4, &opSum, &eSum, &Node::getSum) == 9);
    seg.ch(0, 5, &Node::assign, 10);
    assert(seg.get(0, 4, &opMax, &eMax, &Node::getMax) == 10);
    assert(seg.get(2, 5, &opSum, &eSum, &Node::getSum) == 30);
    seg.ch(2, 4, &Node::chgcd, 3);
    assert(seg.get(1, 3, &opMax, &eMax, &Node::getMax) == 10);
    assert(seg.get(3, 5, &opSum, &eSum, &Node::getSum) == 11);
  }
  {
    constexpr int NUM_CASES = 1000;
    constexpr long long MIN_N = 1;
    constexpr long long MAX_N = 1000;
    constexpr int Q = 1000;
    constexpr long long MIN_VAL = 1;
    constexpr long long MAX_VAL = 1000;
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
            const long long actual = seg.get(l, r, &opMax, &eMax, &Node::getMax);
            // printf("3 %d %d: %lld %lld\n", l, r, expected, actual);
            assert(expected == actual);
          } break;
          case 4: {
            long long expected = 0;
            for (int i = l; i < r; ++i) expected += as[i];
            const long long actual = seg.get(l, r, &opSum, &eSum, &Node::getSum);
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
          const long long res = seg.get(l, r, &opMax, &eMax, &Node::getMax);
          printf("%lld\n", res);
        } break;
        case 4: {
          const long long res = seg.get(l, r, &opSum, &eSum, &Node::getSum);
          printf("%lld\n", res);
        } break;
        default: assert(false);
      }
    }
  }
}

}  // namespace yukicoder880

////////////////////////////////////////////////////////////////////////////////

int main() {
  yukicoder880::unittest();
  // yukicoder880::solve();
  hdu5306::unittest();
  // hdu5306::solve();
  return 0;
}
