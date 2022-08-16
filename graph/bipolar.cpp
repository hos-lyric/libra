#include <assert.h>
#include <vector>

#include "graph.h"

using std::vector;

// Creates us: {0, ..., n-1} -> V,  ord: V -> {0, ..., n-1}
// Bipolar orientation: u -> v  <=>  ord[u] < ord[v]
//   Def.  Every vertex is on some s-t directed path.
// For the graph with V = {s, t}, E = {}, run(s, t) returns false.
struct Bipolar {
  int n;
  Graph g;
  vector<int> us;
  vector<int> ord;

  Bipolar() : n(0), g(), us(), ord() {}
  explicit Bipolar(int n_) : n(n_), g(n_), us(), ord() {}
  void ae(int u, int v) {
    g.ae(u, v);
  }

  // with edge s-t (visited first) added
  int preLen;
  vector<int> pre;
  vector<int> par;
  int zeit;
  vector<int> dis, low;
  void dfs(int u) {
    pre[preLen++] = u;
    dis[u] = low[u] = zeit++;
    for (int j = g.pt[u]; j < g.pt[u + 1]; ++j) {
      const int v = g[j];
      if (~dis[v]) {
        if (low[u] > dis[v]) low[u] = dis[v];
      } else {
        par[v] = u;
        dfs(v);
        if (low[u] > low[v]) low[u] = low[v];
      }
    }
  }
  bool run(int s, int t) {
    assert(0 <= s); assert(s < n);
    assert(0 <= t); assert(t < n);
    assert(s != t);
    us.clear();
    ord.clear();

    g.build(false);
    preLen = 0;
    pre.resize(n);
    par.assign(n, -1);
    zeit = 0;
    dis.assign(n, -1);
    low.assign(n, -1);
    // visit s->t first
    pre[preLen++] = s;
    dis[s] = low[s] = zeit++;
    par[t] = s;
    dfs(t);
    if (n == 2 && g.edges.empty()) {
      // can be a corner case
      return false;
    }
    if (preLen < n) {
      // not connected when s is removed
      return false;
    }
    for (int j = 2; j < preLen; ++j) {
      const int u = pre[j];
      if (dis[par[u]] <= low[u]) {
        // u is an articulation point
        return false;
      }
    }

    vector<int> lef(n, -1), rig(n, -1);
    rig[s] = t;
    lef[t] = s;
    // when visiting u:
    //   if v is a proper ancestor of u:
    //      sides[v] = 0  if v should be to the left of u
    //      sides[v] = 1  if v should be to the right of u
    vector<int> sides(zeit, 0);
    for (int j = 2; j < preLen; ++j) {
      const int u = pre[j];
      const int p = par[u];
      if (sides[low[u]]) {
        // p u r
        const int r = rig[p];
        lef[u] = p;
        rig[u] = r;
        rig[p] = lef[r] = u;
        sides[dis[p]] = 0;
      } else {
        // l u p
        const int l = lef[p];
        lef[u] = l;
        rig[u] = p;
        rig[l] = lef[p] = u;
        sides[dis[p]] = 1;
      }
    }
    us.resize(n);
    us[0] = s;
    for (int j = 0; j < n - 1; ++j) us[j + 1] = rig[us[j]];
    ord.assign(n, -1);
    for (int j = 0; j < n; ++j) ord[us[j]] = j;
    return true;
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <algorithm>
#include <iostream>
#include <utility>

using std::cerr;
using std::endl;
using std::pair;
using std::swap;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void unittest() {
  {
    // Tarjan, Robert Endre. "Two streamlined depth-first search algorithms."
    // Fundamenta Informaticae 9.1 (1986): 85-94.
    Bipolar b(10);
    b.ae(9, 7);
    b.ae(7, 6);
    b.ae(7, 8);
    b.ae(8, 9);
    b.ae(6, 2);
    b.ae(6, 3);
    b.ae(2, 0);
    b.ae(2, 1);
    b.ae(1, 0);
    b.ae(1, 5);
    b.ae(5, 7);
    b.ae(3, 0);
    b.ae(3, 4);
    b.ae(4, 0);
    b.ae(4, 7);
    assert(b.run(0, 9));
    assert(b.us == (vector<int>{0, 1, 5, 2, 4, 3, 6, 7, 8, 9}));
    assert(b.ord == (vector<int>{0, 1, 3, 5, 4, 2, 6, 7, 8, 9}));
  }
  {
    Bipolar b(2);
    assert(!b.run(0, 1));
    assert(!b.run(1, 0));
    b.ae(1, 0);
    assert(b.run(0, 1));
    assert(b.us == (vector<int>{0, 1}));
    assert(b.ord == (vector<int>{0, 1}));
    assert(b.run(1, 0));
    assert(b.us == (vector<int>{1, 0}));
    assert(b.ord == (vector<int>{1, 0}));
    b.ae(0, 1);
    assert(b.run(0, 1));
    assert(b.us == (vector<int>{0, 1}));
    assert(b.ord == (vector<int>{0, 1}));
    assert(b.run(1, 0));
    assert(b.us == (vector<int>{1, 0}));
    assert(b.ord == (vector<int>{1, 0}));
  }
  {
    constexpr int MAX_N = 7;
    constexpr int NUM_CASES = 100;
    for (int n = 3; n <= MAX_N; ++n) {
      for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
        vector<pair<int, int>> edges;
        for (int u = 0; u < n; ++u) for (int v = u + 1; v < n; ++v) {
          if (xrand() & 1) {
            edges.emplace_back(v, u);
          } else {
            edges.emplace_back(u, v);
          }
        }
        const int edgesLen = edges.size();
        for (int i = 0; i < edgesLen; ++i) {
          swap(edges[xrand() % (i + 1)], edges[i]);
        }
        Bipolar b(n);
        for (int i = 0; ; ++i) {
          for (int s = 0; s < n; ++s) for (int t = s + 1; t < n; ++t) {
            auto check = [&](const vector<int> &ord) -> bool {
              vector<int> hasL(n, 0), hasR(n, 0);
              for (int j = 0; j < i; ++j) {
                const int u = edges[j].first, v = edges[j].second;
                if (ord[u] < ord[v]) {
                  hasR[u] = hasL[v] = 1;
                } else {
                  hasR[v] = hasL[u] = 1;
                }
              }
              for (int u = 0; u < n; ++u) if (u != s && u != t) {
                if (!(hasL[u] && hasR[u])) return false;
              }
              return true;
            };
            bool brt = false;
            {
              vector<int> ord(n);
              for (int u = 0; u < n; ++u) ord[u] = u;
              do {
                if (check(ord)) {
                  brt = true;
                  break;
                }
              } while (std::next_permutation(ord.begin(), ord.end()));
            }
            for (int phase = 0; phase < 2; ++phase) {
              const bool res = b.run(s, t);
              if (res) {
                assert(check(b.ord));
              } else {
                assert(b.us.empty());
                assert(b.ord.empty());
              }
              assert(brt == res);
              swap(s, t);
            }
          }
          if (i == edgesLen) break;
          b.ae(edges[i].first, edges[i].second);
        }
      }
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
