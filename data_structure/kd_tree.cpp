#include <assert.h>
#include <algorithm>
#include <utility>
#include <vector>

using std::pair;
using std::vector;

// T: (commutative) monoid representing information of an interval.
//   T()  should return the identity.
//   T(S s)  should represent a single element of the array.
//   T::push(T &l, T &r)  should push the lazy update.
//   T::pull(const T &l, const T &r)  should pull two intervals.
template <class X, class Y, class T> struct KdTree {
  int n, nn;
  // ((x, y), i): permuted
  using Point = pair<pair<X, Y>, int>;
  vector<pair<pair<X, Y>, int>> ps;
  // leaf for point i
  vector<int> us;
  struct Node {
    T t;
    int l, r;
    X minX, maxX;
    Y minY, maxY;
  };
  vector<Node> nodes;
  KdTree() : n(0), nn(0), ps(), us(), nodes() {}
  void add(X x, Y y) {
    const int i = ps.size();
    ps.emplace_back(std::make_pair(x, y), i);
  }
  void build() {
    n = ps.size();
    assert(n >= 1);
    us.resize(n);
    nodes.resize(2 * n - 1);
    buildRec(0, n, 0);
  }
  int buildRec(int jL, int jR, int dir) {
    const int u = nn++;
    Node &node = nodes[u];
    node.minX = node.maxX = ps[jL].first.first;
    node.minY = node.maxY = ps[jL].first.second;
    if (jL + 1 == jR) {
      us[ps[jL].second] = u;
      node.l = node.r = -1;
    } else {
      for (int j = jL + 1; j < jR; ++j) {
        if (node.minX > ps[j].first.first) node.minX = ps[j].first.first;
        if (node.maxX < ps[j].first.first) node.maxX = ps[j].first.first;
        if (node.minY > ps[j].first.second) node.minY = ps[j].first.second;
        if (node.maxY < ps[j].first.second) node.maxY = ps[j].first.second;
      }
      const int jMid = jL + (jR - jL) / 2;
      if (dir == 0) {
        std::nth_element(ps.begin() + jL, ps.begin() + jMid, ps.begin() + jR,
                         [&](const Point &p0, const Point &p1) -> bool {
                           return (p0.first.first < p1.first.first); 
                         });
      } else {
        std::nth_element(ps.begin() + jL, ps.begin() + jMid, ps.begin() + jR,
                         [&](const Point &p0, const Point &p1) -> bool {
                           return (p0.first.second < p1.first.second);
                         });
      }
      node.l = buildRec(jL, jMid, dir ^ 1);
      node.r = buildRec(jMid, jR, dir ^ 1);
    }
    return u;
  }
  const T &all() const {
    return nodes[0].t;
  }
  T &at(int i) {
    return nodes[us[i]].t;
  }
  void pullAll() {
    for (int u = nn; --u >= 0; ) if (~nodes[u].l) pull(u);
  }

  inline void push(int u) {
    nodes[u].t.push(nodes[nodes[u].l].t, nodes[nodes[u].r].t);
  }
  inline void pull(int u) {
    nodes[u].t.pull(nodes[nodes[u].l].t, nodes[nodes[u].r].t);
  }

  // Applies T::f(args...) to point i.
  template <class F, class... Args>
  void chLeaf(int i, F f, Args &&... args) {
    chLeafRec(0, us[i], f, args...);
  }
  template <class F, class... Args>
  void chLeafRec(int u, int leaf, F f, Args &&... args) {
    Node &node = nodes[u];
    if (u == leaf) {
      (node.t.*f)(args...);
      return;
    }
    push(u);
    chLeafRec((leaf < node.r) ? node.l : node.r, leaf, f, args...);
    pull(u);
  }

  // Calculates the value for point i.
  T getLeaf(int i) {
    return getLeafRec(0, us[i]);
  }
  T getLeafRec(int u, int leaf) {
    Node &node = nodes[u];
    if (u == leaf) {
      return node.t;
    }
    push(u);
    const T t = getLeafRec((leaf < node.r) ? node.l : node.r, leaf);
    pull(u);
    return t;
  }

  // Applies T::f(args...) to points in [xa, xb] * [ya, yb].
  template <class F, class... Args>
  void ch(X xa, X xb, Y ya, Y yb, F f, Args &&... args) {
    chRec(0, xa, xb, ya, yb, f, args...);
  }
  template <class F, class... Args>
  void chRec(int u, X xa, X xb, Y ya, Y yb, F f, Args &&... args) {
    Node &node = nodes[u];
    if (xb < node.minX || node.maxX < xa || yb < node.minY || node.maxY < ya) {
      return;
    }
    if (xa <= node.minX && node.maxX <= xb && ya <= node.minY && node.maxY <= yb) {
      (node.t.*f)(args...);
      return;
    }
    push(u);
    chRec(node.l, xa, xb, ya, yb, f, args...);
    chRec(node.r, xa, xb, ya, yb, f, args...);
    pull(u);
  }

  // Calculates the product for points in [xa, xb] * [ya, yb].
  T get(X xa, X xb, Y ya, Y yb) {
    return getRec(0, xa, xb, ya, yb);
  }
  T getRec(int u, X xa, X xb, Y ya, Y yb) {
    Node &node = nodes[u];
    if (xb < node.minX || node.maxX < xa || yb < node.minY || node.maxY < ya) {
      return T();
    }
    if (xa <= node.minX && node.maxX <= xb && ya <= node.minY && node.maxY <= yb) {
      return node.t;
    }
    push(u);
    const T tL = getRec(node.l, xa, xb, ya, yb);
    const T tR = getRec(node.r, xa, xb, ya, yb);
    pull(u);
    T t;
    t.pull(tL, tR);
    return t;
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <random>

using std::cerr;
using std::endl;
using std::mt19937_64;

namespace rect_add_rect_sum {

// add to points in rectangle
// get sum of points in rectangle

using std::max;
using std::min;

struct Node {
  unsigned long long sz, sum;
  unsigned long long lz;
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
  void add(unsigned long long val) {
    sum += sz * val;
    lz += val;
  }
};

void unittest() {
  // small
  {
    KdTree<int, int, Node> kdt;
    kdt.add(0, 14);
    kdt.add(1, 13);
    kdt.add(1, 16);
    kdt.add(2, 15);
    kdt.build();
    kdt.at(0) = 1;
    kdt.at(1) = 10;
    kdt.at(2) = 100;
    kdt.at(3) = 1000;
    kdt.pullAll();
    assert(kdt.all().sum == 1111);
    assert(kdt.get(0, 2, 13, 16).sum == 1111);
    assert(kdt.get(0, 0, 0, 0).sum == 0);
    assert(kdt.get(1, 1, -100, 100).sum == 110);
    assert(kdt.get(-100, 100, 14, 15).sum == 1001);
    kdt.ch(0, 1, 13, 14, &Node::add, 10000);
    assert(kdt.get(0, 2, 13, 16).sum == 21111);
    assert(kdt.get(0, 0, 0, 0).sum == 0);
    assert(kdt.get(1, 1, -100, 100).sum == 10110);
    assert(kdt.get(-100, 100, 14, 15).sum == 11001);
  }
  // large
  {
    mt19937_64 rng;
    constexpr int NUM_CASES = 10000;
    constexpr int MIN_N = 1;
    constexpr int MAX_N = 100;
    constexpr int Q = 1000;
    for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
      const int N = MIN_N + rng() % (MAX_N - MIN_N + 1);
      const long long limX = 1LL << (rng() % 60);
      const long long limY = 1LL << (rng() % 60);
      vector<long long> X(N), Y(N);
      vector<unsigned long long> as(N);
      for (int i = 0; i < N; ++i) {
        X[i] = -limX + rng() % (2 * limX + 1);
        Y[i] = -limY + rng() % (2 * limY + 1);
        as[i] = rng();
      }
      KdTree<long long, long long, Node> kdt;
      for (int i = 0; i < N; ++i) kdt.add(X[i], Y[i]);
      kdt.build();
      for (int i = 0; i < N; ++i) kdt.at(i) = as[i];
      kdt.pullAll();
      for (int q = 0; q < Q; ++q) {
        switch (rng() % 2) {
          case 0: {
            const int i = rng() % N;
            switch (rng() % 2) {
              case 0: {
                const unsigned long long val = rng();
                as[i] += val;
                kdt.chLeaf(i, &Node::add, val);
              } break;
              case 1: {
                assert(kdt.getLeaf(i).sum == as[i]);
              } break;
              default: assert(false);
            }
          } break;
          case 1: {
            long long xa = -limX + rng() % (2 * limX + 1);
            long long xb = -limX + rng() % (2 * limX + 1);
            long long ya = -limY + rng() % (2 * limY + 1);
            long long yb = -limY + rng() % (2 * limY + 1);
            switch (rng() % 2) {
              case 0: {
                const unsigned long long val = rng();
                for (int i = 0; i < N; ++i) if (xa <= X[i] && X[i] <= xb && ya <= Y[i] && Y[i] <= yb) {
                  as[i] += val;
                }
                kdt.ch(xa, xb, ya, yb, &Node::add, val);
              } break;
              case 1: {
                unsigned long long expected = 0;
                for (int i = 0; i < N; ++i) if (xa <= X[i] && X[i] <= xb && ya <= Y[i] && Y[i] <= yb) {
                  expected += as[i];
                }
                assert(kdt.get(xa, xb, ya, yb).sum == expected);
              } break;
              default: assert(false);
            }
          } break;
          default: assert(false);
        }
      }
    }
  }
}

}  // namespace rect_add_rect_sum

////////////////////////////////////////////////////////////////////////////////

int main() {
  rect_add_rect_sum::unittest(); cerr << "PASSED rect_add_rect_sum::unittest" << endl;
  return 0;
}
