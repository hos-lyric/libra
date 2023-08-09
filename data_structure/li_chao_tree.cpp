#include <assert.h>
#include <utility>
#include <vector>

using std::swap;
using std::vector;

// TODO: subsegment

// class Func = TX -> TY
//   for any f, g: Func, [f < g] must be monotone

template <class Func> struct MinLiChaoTree {
  using TX = typename Func::TX;
  using TY = typename Func::TY;
  struct Node {
    int l, r;
    Func f;
  };
  vector<Node> nodes;

  const TX XL, XR;
  int rt;
  MinLiChaoTree() : XL(0), XR(0), rt(-1) {}
  // [L, R)
  MinLiChaoTree(TX XL_, TX XR_) : XL(XL_), XR(XR_), rt(-1) {}
  bool empty() const {
    return (!~rt);
  }
  // Add f to the whole [L, R).
  void add(Func f) {
    int *u = &rt;
    for (TX xL = XL, xR = XR; ; ) {
      if (!~*u) { *u = nodes.size(); nodes.push_back({-1, -1, f}); return; }
      const TX xMid = xL + (xR - xL) / 2;
      if (f(xMid) < nodes[*u].f(xMid)) swap(nodes[*u].f, f);
      if (xL + 1 == xR) return;
      if (f(xL) < nodes[*u].f(xL)) {
        u = &nodes[*u].l; xR = xMid;
      } else if (f(xR) < nodes[*u].f(xR)) {
        u = &nodes[*u].r; xL = xMid;
      } else {
        return;
      }
    }
  }
  // Get min at x.
  TY operator()(TX x) const {
    assert(XL <= x); assert(x < XR);
    assert(!empty());
    int u = rt;
    TY minY = nodes[u].f(x);
    for (TX xL = XL, xR = XR; ; ) {
      const TX xMid = xL + (xR - xL) / 2;
      if (x < xMid) {
        u = nodes[u].l; xR = xMid;
      } else {
        u = nodes[u].r; xL = xMid;
      }
      if (!~u) break;
      const TY y = nodes[u].f(x);
      if (y < minY) minY = y;
    }
    return minY;
  }
};

template <class Func> struct MaxLiChaoTree {
  using TX = typename Func::TX;
  using TY = typename Func::TY;
  struct Node {
    int l, r;
    Func f;
  };
  vector<Node> nodes;

  const TX XL, XR;
  int rt;
  MaxLiChaoTree() : XL(0), XR(0), rt(-1) {}
  // [L, R)
  MaxLiChaoTree(TX XL_, TX XR_) : XL(XL_), XR(XR_), rt(-1) {}
  bool empty() const {
    return (!~rt);
  }
  // Add f to the whole [L, R).
  void add(Func f) {
    int *u = &rt;
    for (TX xL = XL, xR = XR; ; ) {
      if (!~*u) { *u = nodes.size(); nodes.push_back({-1, -1, f}); return; }
      const TX xMid = xL + (xR - xL) / 2;
      if (nodes[*u].f(xMid) < f(xMid)) swap(nodes[*u].f, f);
      if (xL + 1 == xR) return;
      if (nodes[*u].f(xL) < f(xL)) {
        u = &nodes[*u].l; xR = xMid;
      } else if (nodes[*u].f(xR) < f(xR)) {
        u = &nodes[*u].r; xL = xMid;
      } else {
        return;
      }
    }
  }
  // Get max at x.
  TY operator()(TX x) const {
    assert(XL <= x); assert(x < XR);
    assert(!empty());
    int u = rt;
    TY maxY = nodes[u].f(x);
    for (TX xL = XL, xR = XR; ; ) {
      const TX xMid = xL + (xR - xL) / 2;
      if (x < xMid) {
        u = nodes[u].l; xR = xMid;
      } else {
        u = nodes[u].r; xL = xMid;
      }
      if (!~u) break;
      const TY y = nodes[u].f(x);
      if (maxY < y) maxY = y;
    }
    return maxY;
  }
};

// y = p x + q
struct Line {
  using TX = long long;
  using TY = long long;
  long long p, q;
  Line(long long p_, long long q_) : p(p_), q(q_) {}
  TY operator()(TX x) const {
    return p * x + q;
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>

using std::cerr;
using std::endl;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void unittest() {
  {
    MinLiChaoTree<Line> lct(-10, 10);
    assert(lct.empty());
    lct.add(Line(1, 3));
    assert(!lct.empty());
    assert(lct(0) == 3);
    lct.add(Line(2, 6));
    assert(!lct.empty());
    assert(lct(-4) == -2);
    assert(lct(-3) == 0);
    assert(lct(-2) == 1);
    lct.add(Line(1, 4));
    assert(!lct.empty());
    assert(lct(-4) == -2);
    assert(lct(-3) == 0);
    assert(lct(-2) == 1);
    assert(lct(-1) == 2);
    lct.add(Line(5, 9));
    assert(!lct.empty());
    assert(lct(-4) == -11);
    assert(lct(-3) == -6);
    assert(lct(-2) == -1);
    assert(lct(-1) == 2);
    assert(lct(0) == 3);
  }
  {
    MaxLiChaoTree<Line> lct(-10, 10);
    assert(lct.empty());
    lct.add(Line(1, 3));
    assert(!lct.empty());
    assert(lct(0) == 3);
    lct.add(Line(2, 6));
    assert(!lct.empty());
    assert(lct(-4) == -1);
    assert(lct(-3) == 0);
    assert(lct(-2) == 2);
    lct.add(Line(1, 4));
    assert(!lct.empty());
    assert(lct(-4) == 0);
    assert(lct(-3) == 1);
    assert(lct(-2) == 2);
    assert(lct(-1) == 4);
    lct.add(Line(5, 9));
    assert(!lct.empty());
    assert(lct(-4) == 0);
    assert(lct(-3) == 1);
    assert(lct(-2) == 2);
    assert(lct(-1) == 4);
    assert(lct(0) == 9);
  }
  {
    constexpr int NUM_CASES = 1000;
    constexpr int NUM_QUERIES = 1000;
    constexpr long long LIM = -1'000'000'000;
    for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
      long long L, R;
      for (; ; ) {
        L = -LIM + static_cast<long long>(xrand()) % (2 * LIM + 1);
        R = -LIM + static_cast<long long>(xrand()) % (2 * LIM + 1);
        if (L < R) break;
      }
      vector<Line> lines;
      MinLiChaoTree<Line> minLct(L, R);
      MaxLiChaoTree<Line> maxLct(L, R);
      for (int queryId = 0; queryId < NUM_QUERIES; ++queryId) {
        if (lines.empty() || (xrand() & 1)) {
          const long long p = -LIM + static_cast<long long>(xrand()) % (2 * LIM + 1);
          const long long q = -LIM + static_cast<long long>(xrand()) % (2 * LIM + 1);
          const Line line(p, q);
          lines.push_back(line);
          minLct.add(line);
          maxLct.add(line);
        } else {
          const long long x = L + static_cast<long long>(xrand()) % (R - L);
          long long mn = lines[0](x), mx = lines[0](x);
          for (const Line &line : lines) {
            if (mn > line(x)) mn = line(x);
            if (mx < line(x)) mx = line(x);
          }
          assert(mn == minLct(x));
          assert(mx == maxLct(x));
        }
      }
    }
  }
}

#include <stdio.h>

// https://judge.yosupo.jp/problem/line_add_get_min
void yosupoMin_line_add_get_min() {
  constexpr long long LIM_X = 1'000'000'000LL;
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    MinLiChaoTree<Line> lct(-LIM_X, LIM_X + 1);
    for (int i = 0; i < N; ++i) {
      long long a, b;
      scanf("%lld%lld", &a, &b);
      lct.add(Line(a, b));
    }
    for (int q = 0; q < Q; ++q) {
      int typ;
      scanf("%d", &typ);
      switch (typ) {
        case 0: {
          long long a, b;
          scanf("%lld%lld", &a, &b);
          lct.add(Line(a, b));
        } break;
        case 1: {
          long long p;
          scanf("%lld", &p);
          const long long ans = lct(p);
          printf("%lld\n", ans);
        } break;
        default: assert(false);
      }
    }
  }
}
void yosupoMax_line_add_get_min() {
  constexpr long long LIM_X = 1'000'000'000LL;
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    MaxLiChaoTree<Line> lct(-LIM_X, LIM_X + 1);
    for (int i = 0; i < N; ++i) {
      long long a, b;
      scanf("%lld%lld", &a, &b);
      lct.add(Line(-a, -b));
    }
    for (int q = 0; q < Q; ++q) {
      int typ;
      scanf("%d", &typ);
      switch (typ) {
        case 0: {
          long long a, b;
          scanf("%lld%lld", &a, &b);
          lct.add(Line(-a, -b));
        } break;
        case 1: {
          long long p;
          scanf("%lld", &p);
          const long long ans = -lct(p);
          printf("%lld\n", ans);
        } break;
        default: assert(false);
      }
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupoMin_line_add_get_min();
  // yosupoMax_line_add_get_min();
  return 0;
}
