#include <assert.h>
#include <vector>

using std::vector;

// TODO
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

  template <class F, class... Args> void chRec(int u, F f, const Args &... args) {
    if ((ts[u].*f)(args...)) return;
    push(u);
    chRec(u << 1, f, args...);
    chRec(u << 1 | 1, f, args...);
    merge(u);
  }
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

  template <class Op, class E, class F, class... Args> auto get(int a, int b, Op op, E e, F f, const Args &... args) {
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
  long long lz;
  Node() : lcm(1), mx(0), sz(0), sum(0), lz(-1) {}
  Node(long long val) : lcm(val), mx(val), sz(1), sum(val), lz(-1) {}
  void push(Node &l, Node &r) {
    if (lz != -1) {
      l.assign(lz);
      r.assign(lz);
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
    const vector<long long> as{1, 6, 8, 7, 3};
    SegmentTreeRec<Node> seg(as);
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
}

void brute() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    vector<long long> A(N);
    for (int i = 0; i < N; ++i) {
      scanf("%lld", &A[i]);
    }
    for (int q = 0; q < Q; ++q) {
      int typ, l, r;
      scanf("%d%d%d", &typ, &l, &r);
      --l;
      switch (typ) {
        case 1: {
          long long x;
          scanf("%lld", &x);
          for (int i = l; i < r; ++i) A[i] = x;
        } break;
        case 2: {
          long long x;
          scanf("%lld", &x);
          for (int i = l; i < r; ++i) A[i] = gcd(A[i], x);
        } break;
        case 3: {
          long long mx = 0;
          for (int i = l; i < r; ++i) if (mx < A[i]) mx = A[i];
          printf("%lld\n", mx);
        } break;
        case 4: {
          long long sum = 0;
          for (int i = l; i < r; ++i) sum += A[i];
          printf("%lld\n", sum);
        } break;
        default: assert(false);
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
  // yukicoder880::unittest();
  // yukicoder880::brute();
  yukicoder880::solve();
  return 0;
}