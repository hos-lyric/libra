#include <assert.h>
#include <vector>

using std::vector;

// T: monoid representing information of an interval.
//   T()  should return the identity.
//   T(S s)  should represent a single element of the array.
//   T::push(T &l, T &r)  should push the lazy update.
//   T::pull(const T &l, const T &r)  should pull two intervals.
template <class T> struct SegmentTreeRange {
  int logN, n;
  vector<T> ts;
  SegmentTreeRange() {}
  explicit SegmentTreeRange(int n_) {
    for (logN = 0, n = 1; n < n_; ++logN, n <<= 1) {}
    ts.resize(n << 1);
  }
  template <class S> explicit SegmentTreeRange(const vector<S> &ss) {
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
      if (aa & 1) (ts[aa++].*f)(args...);
      if (bb & 1) (ts[--bb].*f)(args...);
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

namespace range_add_range_sum {

//   update range  a[i] <- a[i] + b
//   get  sum a[l, r)

using std::max;
using std::min;

struct Node {
  long long sz, sum;
  long long lz;
  Node() : sz(0), sum(0), lz(0) {}
  Node(long long val) : sz(1), sum(val), lz(0) {}
  void push(Node &l, Node &r) {
    l.add(lz);
    r.add(lz);
    lz = 0;
  }
  void pull(const Node &l, const Node &r) {
    sz = l.sz + r.sz;
    sum = l.sum + r.sum;
  }
  void add(long long val) {
    sum += sz * val;
    lz += val;
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

long long getSum(SegmentTreeRange<Node> &seg, int a, int b) {
  return seg.get(a, b,
                 [&](long long l, long long r) -> long long { return l + r; },
                 [&]() -> long long { return 0LL; },
                 &Node::getSum);
}

// (sum of [a, b)) >= target
int findRight(SegmentTreeRange<Node> &seg, int a, long long tar) {
  long long acc = 0;
  return seg.findRight(a, &Node::accSum, acc, tar);
}
int findLeft(SegmentTreeRange<Node> &seg, int b, long long tar) {
  long long acc = 0;
  return seg.findLeft(b, &Node::accSum, acc, tar);
}

void unittest() {
  // small
  {
    SegmentTreeRange<Node> seg(vector<long long>{1, 2, 3, 4, 5});
    // [1, 2, 3, 4, 5]
    assert(getSum(seg, 0, 5) == 15);
    assert(seg.get(0, 5).sum == 15);
    assert(findRight(seg, 1, 4) == 3);
    assert(findLeft(seg, 3, 5) == 1);
    seg.ch(2, 4, &Node::add, 100);
    // [1, 2, 103, 104, 5]
    assert(seg.get(0, 3).sum == 106);
    assert(getSum(seg, 0, 3) == 106);
    assert(findRight(seg, 0, 210) == 4);
    assert(findLeft(seg, 5, 216) == -1);
    seg.ch(0, 5, &Node::add, 10);
    // [11, 12, 113, 114, 15]
    assert(getSum(seg, 2, 5) == 242);
    assert(seg.get(2, 5).sum == 242);
    assert(findRight(seg, 2, 243) == seg.n + 1);
    assert(findLeft(seg, 4, 250) == 0);
  }
  // large
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
      SegmentTreeRange<Node> seg(as);
      for (int q = 0; q < Q; ++q) {
        int l, r;
        for (; ; ) {
          l = xrand() % (N + 1);
          r = xrand() % (N + 1);
          if (l <= r) {
            break;
          }
        }
        switch (xrand() % 4) {
          case 0: {
            const long long b = MIN_VAL + xrand() % (MAX_VAL - MIN_VAL + 1);
            // printf("0 %d %d %lld\n", l, r, b);
            for (int i = l; i < r; ++i) as[i] += b;
            seg.ch(l, r, &Node::add, b);
          } break;
          case 1: {
            long long expected = 0;
            for (int i = l; i < r; ++i) expected += as[i];
            const long long actual = getSum(seg, l, r);
            // printf("1 %d %d: %lld %lld\n", l, r, expected, actual);
            assert(expected == actual);
          } break;
          case 2: {
            if (l == r || as[r - 1] > 0) {
              long long b = 0;
              for (int i = l; i < r; ++i) b += as[i];
              if (l != r) b -= xrand() % as[r - 1];
              const int actual = findRight(seg, l, b);
              // printf("2 %d %lld: %d %d\n", l, b, r, actual);
              assert(r == actual);
            } else {
              long long b = 0;
              for (int i = l; i < N; ++i) b += as[i];
              b += 1 + xrand() % MAX_VAL;
              const int actual = findRight(seg, l, b);
              // printf("2 %d %lld: %d %d\n", l, b, seg.n + 1, actual);
              assert(seg.n + 1 == actual);
            }
          } break;
          case 3: {
            if (l == r || as[l] > 0) {
              long long b = 0;
              for (int i = r; --i >= l; ) b += as[i];
              if (l != r) b -= xrand() % as[l];
              const int actual = findLeft(seg, r, b);
              // printf("3 %d %lld: %d %d\n", r, b, l, actual);
              assert(l == actual);
            } else {
              long long b = 0;
              for (int i = r; --i >= 0; ) b += as[i];
              b += 1 + xrand() % MAX_VAL;
              const int actual = findLeft(seg, r, b);
              // printf("3 %d %lld: %d %d\n", l, b, -1, actual);
              assert(-1 == actual);
            }
          } break;
          default: assert(false);
        }
      }
    }
  }
}

}  // namespace range_add_range_sum

////////////////////////////////////////////////////////////////////////////////

namespace yosupo_range_affine_range_sum {

// https://judge.yosupo.jp/problem/range_affine_range_sum
//   update range  a[i] <- b a[i] + c
//   get  sum a[l, r)

constexpr long long MO = 998244353;

struct Node {
  long long sz, sum;
  long long lzB, lzC;
  Node() : sz(0), sum(0), lzB(1), lzC(0) {}
  Node(long long val) : sz(1), sum(val), lzB(1), lzC(0) {}
  void push(Node &l, Node &r) {
    l.ch(lzB, lzC);
    r.ch(lzB, lzC);
    lzB = 1;
    lzC = 0;
  }
  void pull(const Node &l, const Node &r) {
    sz = (l.sz + r.sz) % MO;
    sum = (l.sum + r.sum) % MO;
  }
  void ch(long long b, long long c) {
    sum = (b * sum + c * sz) % MO;
    lzB = (lzB * b) % MO;
    lzC = (lzC * b + c) % MO;
  }
  long long getSum() const {
    return sum;
  }
};

long long getSum(SegmentTreeRange<Node> &seg, int a, int b) {
  return seg.get(a, b,
                 [&](long long l, long long r) -> long long { return (l + r) % MO; },
                 [&]() -> long long { return 0; },
                 &Node::getSum);
}

void unittest() {
  {
    SegmentTreeRange<Node> seg(vector<long long>{1, 2, 3, 4, 5});
    assert(getSum(seg, 0, 5) == 15);
    seg.ch(2, 4, &Node::ch, 100, 101);
    assert(getSum(seg, 0, 3) == 404);
    seg.ch(1, 3, &Node::ch, 102, 103);
    assert(getSum(seg, 2, 5) == 41511);
    seg.ch(2, 5, &Node::ch, 104, 105);
    assert(getSum(seg, 0, 5) == 4317767);
  }
}

void solve() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    vector<long long> A(N);
    for (int i = 0; i < N; ++i) {
      scanf("%lld", &A[i]);
    }
    SegmentTreeRange<Node> seg(A);
    for (int q = 0; q < Q; ++q) {
      int typ, l, r;
      scanf("%d%d%d", &typ, &l, &r);
      switch (typ) {
        case 0: {
          long long b, c;
          scanf("%lld%lld", &b, &c);
          seg.ch(l, r, &Node::ch, b, c);
        } break;
        case 1: {
          const long long res = getSum(seg, l, r);
          printf("%lld\n", res);
        } break;
        default: assert(false);
      }
    }
  }
}

}  // namespace yosupo_range_affine_range_sum

////////////////////////////////////////////////////////////////////////////////

void unittests() {
  range_add_range_sum::unittest(); cerr << "PASSED range_add_range_sum::unittest" << endl;
  yosupo_range_affine_range_sum::unittest(); cerr << "PASSED yosupo_range_affine_range_sum::unittest" << endl;
}

int main() {
  unittests();
  // yosupo_range_affine_range_sum::solve();
  return 0;
}
