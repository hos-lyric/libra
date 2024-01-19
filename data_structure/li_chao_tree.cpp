#include <assert.h>
#include <utility>
#include <vector>

using std::pair;
using std::swap;
using std::vector;

// class Func = TX -> TY
//   Uses TY::operator< for comparison.
//   For any f, g: Func, [f < g] must be monotone on [XL, XR).

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
  // [XL, XR)
  MinLiChaoTree(TX XL_, TX XR_) : XL(XL_), XR(XR_), rt(-1) {}
  bool empty() const {
    return (!~rt);
  }
  // Add f to the whole [XL, XR).
  void add(Func f) {
    int *u = &rt;
    for (TX xL = XL, xR = XR; ; ) {
      if (!~*u) { *u = nodes.size(); nodes.push_back({-1, -1, f}); return; }
      const TX xMid = xL + (xR - xL) / 2;
      if (f(xMid) < nodes[*u].f(xMid)) swap(nodes[*u].f, f);
      if (xL + 1 == xR) return;
      if (f(xL) < nodes[*u].f(xL)) {
        u = &nodes[*u].l; xR = xMid;
      } else if (f(xR - 1) < nodes[*u].f(xR - 1)) {
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
};  // MinLiChaoTree

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
  // [XL, XR)
  MaxLiChaoTree(TX XL_, TX XR_) : XL(XL_), XR(XR_), rt(-1) {}
  bool empty() const {
    return (!~rt);
  }
  // Add f to the whole [XL, XR).
  void add(Func f) {
    int *u = &rt;
    for (TX xL = XL, xR = XR; ; ) {
      if (!~*u) { *u = nodes.size(); nodes.push_back({-1, -1, f}); return; }
      const TX xMid = xL + (xR - xL) / 2;
      if (nodes[*u].f(xMid) < f(xMid)) swap(nodes[*u].f, f);
      if (xL + 1 == xR) return;
      if (nodes[*u].f(xL) < f(xL)) {
        u = &nodes[*u].l; xR = xMid;
      } else if (nodes[*u].f(xR - 1) < f(xR - 1)) {
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
};  // MaxLiChaoTree

template <class Func> struct MinLiChaoTreeSegment {
  using TX = typename Func::TX;
  using TY = typename Func::TY;
  struct Node {
    int l, r;
    bool has;
    Func f;
  };
  vector<Node> nodes;

  const TX XL, XR;
  int rt;
  MinLiChaoTreeSegment() : XL(0), XR(0), rt(-1) {}
  // [XL, XR)
  MinLiChaoTreeSegment(TX XL_, TX XR_) : XL(XL_), XR(XR_), rt(-1) {}
  // Add f to the whole [XL, XR).
  void add(const Func &f) {
    addSub(&rt, XL, XR, f);
  }
  // Add f to [xA, xB).
  void add(TX xA, TX xB, const Func &f) {
    assert(XL <= xA); assert(xA <= xB); assert(xB <= XR);
    rt = addRec(rt, XL, XR, xA, xB, f);
  }
  // Get min at x.
  // Returns (true, min at x) or (false, TY())
  pair<bool, TY> operator()(TX x) const {
    assert(XL <= x); assert(x < XR);
    pair<bool, TY> minY(false, TY());
    int u = rt;
    for (TX xL = XL, xR = XR; ~u; ) {
      if (nodes[u].has) {
        const TY y = nodes[u].f(x);
        if (!minY.first || y < minY.second) minY = std::make_pair(true, y);
      }
      const TX xMid = xL + (xR - xL) / 2;
      if (x < xMid) {
        u = nodes[u].l; xR = xMid;
      } else {
        u = nodes[u].r; xL = xMid;
      }
    }
    return minY;
  }

  void addSub(int *u, TX xL, TX xR, Func f) {
    for (; ; ) {
      if (!~*u) { *u = nodes.size(); nodes.push_back({-1, -1, true, f}); return; }
      if (!nodes[*u].has) { nodes[*u].has = true; nodes[*u].f = f; return; }
      const TX xMid = xL + (xR - xL) / 2;
      if (f(xMid) < nodes[*u].f(xMid)) swap(nodes[*u].f, f);
      if (xL + 1 == xR) return;
      if (f(xL) < nodes[*u].f(xL)) {
        u = &nodes[*u].l; xR = xMid;
      } else if (f(xR - 1) < nodes[*u].f(xR - 1)) {
        u = &nodes[*u].r; xL = xMid;
      } else {
        return;
      }
    }
  }
  int addRec(int u, TX xL, TX xR, TX xA, TX xB, const Func &f) {
    if (xB <= xL || xR <= xA) return u;
    if (xA <= xL && xR <= xB) { int v = u; addSub(&v, xL, xR, f); return v; }
    if (~u && nodes[u].has && nodes[u].f(xL) < f(xL) && nodes[u].f(xR - 1) < f(xR - 1)) return u;
    if (!~u) { u = nodes.size(); nodes.push_back({-1, -1, false, Func()}); }
    const TX xMid = xL + (xR - xL) / 2;
    const int uL = addRec(nodes[u].l, xL, xMid, xA, xB, f); nodes[u].l = uL;
    const int uR = addRec(nodes[u].r, xMid, xR, xA, xB, f); nodes[u].r = uR;
    return u;
  }
};  // MinLiChaoTreeSegment

template <class Func> struct MaxLiChaoTreeSegment {
  using TX = typename Func::TX;
  using TY = typename Func::TY;
  struct Node {
    int l, r;
    bool has;
    Func f;
  };
  vector<Node> nodes;

  const TX XL, XR;
  int rt;
  MaxLiChaoTreeSegment() : XL(0), XR(0), rt(-1) {}
  // [XL, XR)
  MaxLiChaoTreeSegment(TX XL_, TX XR_) : XL(XL_), XR(XR_), rt(-1) {}
  // Add f to the whole [XL, XR).
  void add(const Func &f) {
    addSub(&rt, XL, XR, f);
  }
  // Add f to [xA, xB).
  void add(TX xA, TX xB, const Func &f) {
    assert(XL <= xA); assert(xA <= xB); assert(xB <= XR);
    rt = addRec(rt, XL, XR, xA, xB, f);
  }
  // Get max at x.
  // Returns (true, max at x) or (false, TY())
  pair<bool, TY> operator()(TX x) const {
    assert(XL <= x); assert(x < XR);
    pair<bool, TY> maxY(false, TY());
    int u = rt;
    for (TX xL = XL, xR = XR; ~u; ) {
      if (nodes[u].has) {
        const TY y = nodes[u].f(x);
        if (!maxY.first || maxY.second < y) maxY = std::make_pair(true, y);
      }
      const TX xMid = xL + (xR - xL) / 2;
      if (x < xMid) {
        u = nodes[u].l; xR = xMid;
      } else {
        u = nodes[u].r; xL = xMid;
      }
    }
    return maxY;
  }

  void addSub(int *u, TX xL, TX xR, Func f) {
    for (; ; ) {
      if (!~*u) { *u = nodes.size(); nodes.push_back({-1, -1, true, f}); return; }
      if (!nodes[*u].has) { nodes[*u].has = true; nodes[*u].f = f; return; }
      const TX xMid = xL + (xR - xL) / 2;
      if (nodes[*u].f(xMid) < f(xMid)) swap(nodes[*u].f, f);
      if (xL + 1 == xR) return;
      if (nodes[*u].f(xL) < f(xL)) {
        u = &nodes[*u].l; xR = xMid;
      } else if (nodes[*u].f(xR - 1) < f(xR - 1)) {
        u = &nodes[*u].r; xL = xMid;
      } else {
        return;
      }
    }
  }
  int addRec(int u, TX xL, TX xR, TX xA, TX xB, const Func &f) {
    if (xB <= xL || xR <= xA) return u;
    if (xA <= xL && xR <= xB) { int v = u; addSub(&v, xL, xR, f); return v; }
    if (~u && nodes[u].has && f(xL) < nodes[u].f(xL) && f(xR - 1) < nodes[u].f(xR - 1)) return u;
    if (!~u) { u = nodes.size(); nodes.push_back({-1, -1, false, Func()}); }
    const TX xMid = xL + (xR - xL) / 2;
    const int uL = addRec(nodes[u].l, xL, xMid, xA, xB, f); nodes[u].l = uL;
    const int uR = addRec(nodes[u].r, xMid, xR, xA, xB, f); nodes[u].r = uR;
    return u;
  }
};  // MaxLiChaoTreeSegment

// y = p x + q
struct Line {
  using TX = long long;
  using TY = long long;
  long long p, q;
  Line() {}
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
          assert(minLct(x) == mn);
          assert(maxLct(x) == mx);
        }
      }
    }
  }
}

// y = p x + q
struct LineTester {
  using TX = long long;
  using TY = long long;
  bool has;
  long long p, q;
  LineTester() : has(false), p(0), q(0) {}
  LineTester(long long p_, long long q_) : has(true), p(p_), q(q_) {}
  TY operator()(TX x) const {
    assert(has);
    return p * x + q;
  }
};

void unittest_Segment() {
  using Pair = pair<bool, LineTester::TY>;
  {
    MinLiChaoTreeSegment<LineTester> lct(-10, 10);
    lct.add(-6, 6, LineTester(1, 3));
    assert(lct(-7) == Pair(false, 0));
    assert(lct(-6) == Pair(true, -3));
    assert(lct(5) == Pair(true, 8));
    assert(lct(6) == Pair(false, 0));
    lct.add(-4, 0, LineTester(2, 6));
    assert(lct(-5) == Pair(true, -2));
    assert(lct(-4) == Pair(true, -2));
    assert(lct(-3) == Pair(true, 0));
    assert(lct(-2) == Pair(true, 1));
    assert(lct(-1) == Pair(true, 2));
    assert(lct(0) == Pair(true, 3));
    lct.add(-2, 2, LineTester(1, 4));
    assert(lct(-3) == Pair(true, 0));
    assert(lct(-2) == Pair(true, 1));
    assert(lct(-1) == Pair(true, 2));
    assert(lct(0) == Pair(true, 3));
    assert(lct(1) == Pair(true, 4));
    assert(lct(2) == Pair(true, 5));
    lct.add(-2, 1, LineTester(5, 9));
    assert(lct(-3) == Pair(true, 0));
    assert(lct(-2) == Pair(true, -1));
    assert(lct(-1) == Pair(true, 2));
    assert(lct(0) == Pair(true, 3));
    assert(lct(1) == Pair(true, 4));
  }
  {
    MaxLiChaoTreeSegment<LineTester> lct(-10, 10);
    lct.add(-6, 6, LineTester(1, 3));
    assert(lct(-7) == Pair(false, 0));
    assert(lct(-6) == Pair(true, -3));
    assert(lct(5) == Pair(true, 8));
    assert(lct(6) == Pair(false, 0));
    lct.add(-4, 0, LineTester(2, 6));
    assert(lct(-5) == Pair(true, -2));
    assert(lct(-4) == Pair(true, -1));
    assert(lct(-3) == Pair(true, 0));
    assert(lct(-2) == Pair(true, 2));
    assert(lct(-1) == Pair(true, 4));
    assert(lct(0) == Pair(true, 3));
    lct.add(-2, 2, LineTester(1, 4));
    assert(lct(-3) == Pair(true, 0));
    assert(lct(-2) == Pair(true, 2));
    assert(lct(-1) == Pair(true, 4));
    assert(lct(0) == Pair(true, 4));
    assert(lct(1) == Pair(true, 5));
    assert(lct(2) == Pair(true, 5));
    lct.add(-2, 1, LineTester(5, 9));
    assert(lct(-3) == Pair(true, 0));
    assert(lct(-2) == Pair(true, 2));
    assert(lct(-1) == Pair(true, 4));
    assert(lct(0) == Pair(true, 9));
    assert(lct(1) == Pair(true, 5));
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
      vector<pair<pair<long long, long long>, LineTester>> lineSegments;
      MinLiChaoTreeSegment<LineTester> minLct(L, R);
      MaxLiChaoTreeSegment<LineTester> maxLct(L, R);
      for (int queryId = 0; queryId < NUM_QUERIES; ++queryId) {
        if (xrand() & 1) {
          long long a, b;
          if (xrand() % 100 == 0) {
            a = L;
            b = R;
          } else {
            for (; ; ) {
              a = L + static_cast<long long>(xrand()) % (R - L);
              b = L + static_cast<long long>(xrand()) % (R - L) + 1;
              if (a < b) break;
            }
          }
          const long long p = -LIM + static_cast<long long>(xrand()) % (2 * LIM + 1);
          const long long q = -LIM + static_cast<long long>(xrand()) % (2 * LIM + 1);
          const LineTester line(p, q);
          lineSegments.emplace_back(std::make_pair(a, b), line);
          if (a == L && b == R) {
            minLct.add(line);
            maxLct.add(line);
          } else {
            minLct.add(a, b, line);
            maxLct.add(a, b, line);
          }
        } else {
          const long long x = L + static_cast<long long>(xrand()) % (R - L);
          bool has = false;
          long long mn = 0, mx = 0;
          for (const auto &lineSegment : lineSegments) {
            if (lineSegment.first.first <= x && x < lineSegment.first.second) {
              const LineTester &line = lineSegment.second;
              if (has) {
                if (mn > line(x)) mn = line(x);
                if (mx < line(x)) mx = line(x);
              } else {
                has = true;
                mn = mx = line(x);
              }
            }
          }
          assert(minLct(x) == Pair(has, mn));
          assert(maxLct(x) == Pair(has, mx));
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

// https://judge.yosupo.jp/problem/segment_add_get_min
void yosupoMin_segment_add_get_min() {
  constexpr long long LIM_X = 1'000'000'000LL;
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    MinLiChaoTreeSegment<Line> lct(-LIM_X, LIM_X + 1);
    for (int i = 0; i < N; ++i) {
      long long l, r, a, b;
      scanf("%lld%lld%lld%lld", &l, &r, &a, &b);
      lct.add(l, r, Line(a, b));
    }
    for (int q = 0; q < Q; ++q) {
      int typ;
      scanf("%d", &typ);
      switch (typ) {
        case 0: {
          long long l, r, a, b;
          scanf("%lld%lld%lld%lld", &l, &r, &a, &b);
          lct.add(l, r, Line(a, b));
        } break;
        case 1: {
          long long p;
          scanf("%lld", &p);
          const pair<bool, long long> ans = lct(p);
          if (ans.first) {
            printf("%lld\n", ans.second);
          } else {
            puts("INFINITY");
          }
        } break;
        default: assert(false);
      }
    }
  }
}
void yosupoMax_segment_add_get_min() {
  constexpr long long LIM_X = 1'000'000'000LL;
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    MaxLiChaoTreeSegment<Line> lct(-LIM_X, LIM_X + 1);
    for (int i = 0; i < N; ++i) {
      long long l, r, a, b;
      scanf("%lld%lld%lld%lld", &l, &r, &a, &b);
      lct.add(l, r, Line(-a, -b));
    }
    for (int q = 0; q < Q; ++q) {
      int typ;
      scanf("%d", &typ);
      switch (typ) {
        case 0: {
          long long l, r, a, b;
          scanf("%lld%lld%lld%lld", &l, &r, &a, &b);
          lct.add(l, r, Line(-a, -b));
        } break;
        case 1: {
          long long p;
          scanf("%lld", &p);
          const pair<bool, long long> ans = lct(p);
          if (ans.first) {
            printf("%lld\n", -ans.second);
          } else {
            puts("INFINITY");
          }
        } break;
        default: assert(false);
      }
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  unittest_Segment(); cerr << "PASSED unittest_Segment" << endl;
  // yosupoMin_line_add_get_min();
  // yosupoMax_line_add_get_min();
  // yosupoMin_segment_add_get_min();
  // yosupoMax_segment_add_get_min();
  return 0;
}
