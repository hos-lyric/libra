#include <assert.h>
#include <vector>

#include "graph.h"

using std::vector;

// gg: bipartite graph between {vertex} and {biconnected component}
//   (gg.n - n) biconnected components
// f: DFS forest
struct Biconnected {
  int n;
  Graph g, f, gg;

  Biconnected() : n(0), stackLen(0), zeit(0) {}
  explicit Biconnected(int n_) : n(n_), g(n_), stackLen(0), zeit(0) {}
  void ae(int u, int v) {
    g.ae(u, v);
  }

  int stackLen;
  vector<int> stack;
  vector<int> par, rs;
  int zeit;
  vector<int> dis, fin, low;
  void dfs(int u) {
    stack[stackLen++] = u;
    dis[u] = low[u] = zeit++;
    for (int j = g.pt[u]; j < g.pt[u + 1]; ++j) {
      const int v = g[j];
      if (~dis[v]) {
        if (low[u] > dis[v]) low[u] = dis[v];
      } else {
        f.ae(u, v);
        par[v] = u;
        rs[v] = rs[u];
        dfs(v);
        if (low[u] > low[v]) low[u] = low[v];
        if (dis[u] == low[v]) {
          const int x = gg.n++;
          for (; ; ) {
            const int w = stack[--stackLen];
            gg.ae(w, x);
            if (w == v) break;
          }
          gg.ae(u, x);
        }
      }
    }
    fin[u] = zeit;
  }
  void build() {
    g.build(false);
    f = Graph(n);
    gg = Graph(n);
    stack.resize(n);
    par.assign(n, -1);
    rs.assign(n, -1);
    zeit = 0;
    dis.assign(n, -1);
    fin.assign(n, -1);
    low.assign(n, -1);
    for (int u = 0; u < n; ++u) if (!~dis[u]) {
      stackLen = 0;
      rs[u] = u;
      dfs(u);
    }
    f.build(true);
    gg.build(false);
  }

  // Returns true iff u is an articulation point
  //   <=> # of connected components increases when u is removed.
  inline bool isArt(int u) const {
    return (gg.deg(u) >= 2);
  }

  // Returns w s.t. w is a child of u and a descendant of v in the DFS forest.
  // Returns -1 instead if v is not a proper descendant of u
  //   O(log(deg(u))) time
  int dive(int u, int v) const {
    if (dis[u] < dis[v] && dis[v] < fin[u]) {
      int j0 = f.pt[u], j1 = f.pt[u + 1];
      for (; j0 + 1 < j1; ) {
        const int j = (j0 + j1) / 2;
        ((dis[f[j]] <= dis[v]) ? j0 : j1) = j;
      }
      return f[j0];
    } else {
      return -1;
    }
  }
  // Returns true iff there exists a v-w path when u is removed.
  //   O(log(deg(u))) time
  bool isStillReachable(int u, int v, int w) const {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    assert(0 <= w); assert(w < n);
    assert(u != v);
    assert(u != w);
    if (rs[v] != rs[w]) return false;
    if (rs[u] != rs[v]) return true;
    const int vv = dive(u, v);
    const int ww = dive(u, w);
    if (~vv) {
      if (~ww) {
        return (vv == ww || (dis[u] > low[vv] && dis[u] > low[ww]));
      } else {
        return (dis[u] > low[vv]);
      }
    } else {
      if (~ww) {
        return (dis[u] > low[ww]);
      } else {
        return true;
      }
    }
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <sstream>

using std::cerr;
using std::endl;
using std::ostringstream;

void test_dive(const Biconnected &b) {
  const int n = b.n;
  vector<vector<int>> d(n, vector<int>(n, n));
  for (int u = 0; u < n; ++u) d[u][u] = 0;
  for (const auto edge : b.f.edges) {
    const int u = edge.first, v = edge.second;
    d[u][v] = d[v][u] = 1;
  }
  for (int w = 0; w < n; ++w) for (int u = 0; u < n; ++u) for (int v = 0; v < n; ++v) {
    if (d[u][v] > d[u][w] + d[w][v]) {
      d[u][v] = d[u][w] + d[w][v];
    }
  }
  for (int u = 0; u < n; ++u) {
    int r = u;
    for (int v = 0; v < n; ++v) if (d[u][v] < n) {
      if (r > v) {
        r = v;
      }
    }
    for (int v = 0; v < n; ++v) {
      int vv = -1;
      if (d[u][v] < n && u != v && d[r][u] + d[u][v] == d[r][v]) {
        for (int w = 0; w < n; ++w) if (d[u][w] == 1 && d[r][u] + 1 == d[r][w] && d[u][v] == 1 + d[w][v]) {
          assert(!~vv);
          vv = w;
        }
      }
      assert(vv == b.dive(u, v));
    }
  }
}

void test_isStillReachable(const Biconnected &b) {
  const int n = b.n;
  for (int t = 0; t < n; ++t) {
    vector<vector<int>> d(n, vector<int>(n, n));
    for (int u = 0; u < n; ++u) if (t != u) d[u][u] = 0;
    for (const auto edge : b.g.edges) {
      const int u = edge.first, v = edge.second;
      if (t != u && t != v) d[u][v] = d[v][u] = 1;
    }
    for (int w = 0; w < n; ++w) for (int u = 0; u < n; ++u) for (int v = 0; v < n; ++v) {
      if (d[u][v] > d[u][w] + d[w][v]) {
        d[u][v] = d[u][w] + d[w][v];
      }
    }
    for (int u = 0; u < n; ++u) for (int v = 0; v < n; ++v) if (t != u && t != v) {
      assert((d[u][v] < n) == b.isStillReachable(t, u, v));
    }
  }
}

void unittest() {
  {
    Biconnected b(0);
    b.build();
    {
      ostringstream oss;
      oss << b.g;
      assert(oss.str() == "Graph(n=0;)");
    }
    {
      ostringstream oss;
      oss << b.f;
      assert(oss.str() == "Graph(n=0;)");
    }
    {
      ostringstream oss;
      oss << b.gg;
      assert(oss.str() == "Graph(n=0;)");
    }
  }
  {
    Biconnected b(1);
    b.ae(0, 0);
    b.build();
    {
      ostringstream oss;
      oss << b.g;
      assert(oss.str() == "Graph(n=1; 0:[0,0])");
    }
    {
      ostringstream oss;
      oss << b.f;
      assert(oss.str() == "Graph(n=1; 0:[])");
    }
    {
      ostringstream oss;
      oss << b.gg;
      assert(oss.str() == "Graph(n=1; 0:[])");
    }
    assert(!b.isArt(0));
  }
  {
    Biconnected b(2);
    b.ae(0, 1);
    b.ae(1, 0);
    b.build();
    {
      ostringstream oss;
      oss << b.g;
      assert(oss.str() == "Graph(n=2; 0:[1,1] 1:[0,0])");
    }
    {
      ostringstream oss;
      oss << b.f;
      assert(oss.str() == "Graph(n=2; 0:[1] 1:[])");
    }
    {
      ostringstream oss;
      oss << b.gg;
      assert(oss.str() == "Graph(n=3; 0:[2] 1:[2] 2:[1,0])");
    }
    assert(!b.isArt(0));
    assert(!b.isArt(1));
    assert(b.isStillReachable(0, 1, 1));
    assert(b.isStillReachable(1, 0, 0));
  }
  {
    // Biconnected b;
    // b = Biconnected(5);
    Biconnected b(5);
    b.ae(0, 1);
    b.ae(0, 2);
    b.ae(1, 2);
    b.ae(1, 3);
    b.ae(1, 4);
    b.ae(3, 4);
    b.build();
    {
      ostringstream oss;
      oss << b.g;
      assert(oss.str() == "Graph(n=5; 0:[1,2] 1:[0,2,3,4] 2:[0,1] 3:[1,4] 4:[1,3])");
    }
    {
      ostringstream oss;
      oss << b.f;
      assert(oss.str() == "Graph(n=5; 0:[1] 1:[2,3] 2:[] 3:[4] 4:[])");
    }
    {
      ostringstream oss;
      oss << b.gg;
      assert(oss.str() == "Graph(n=7; 0:[6] 1:[5,6] 2:[6] 3:[5] 4:[5] 5:[4,3,1] 6:[2,1,0])");
    }
    assert(!b.isArt(0));
    assert(b.isArt(1));
    assert(!b.isArt(2));
    assert(!b.isArt(3));
    assert(!b.isArt(4));
    test_dive(b);
    test_isStillReachable(b);
  }
  {
    Biconnected b(20);
    b.ae(0, 2);
    b.ae(0, 3);
    b.ae(0, 4);
    b.ae(2, 3);
    b.ae(3, 4);
    b.ae(1, 18);
    b.ae(1, 19);
    b.ae(0, 8);
    b.ae(6, 7);
    b.ae(7, 8);
    b.ae(8, 6);
    b.ae(8, 9);
    b.ae(9, 10);
    b.ae(10, 16);
    b.ae(16, 8);
    b.ae(8, 10);
    b.ae(9, 16);
    b.ae(16, 16);
    b.ae(11, 16);
    b.ae(12, 13);
    b.ae(14, 16);
    b.ae(16, 17);
    b.ae(12, 17);
    b.ae(13, 14);
    b.build();
    {
      ostringstream oss;
      oss << b.g;
      assert(oss.str() == "Graph(n=20;"
          " 0:[2,3,4,8] 1:[18,19] 2:[0,3] 3:[0,2,4] 4:[0,3]"
          " 5:[] 6:[7,8] 7:[6,8] 8:[0,7,6,9,16,10] 9:[8,10,16]"
          " 10:[9,16,8] 11:[16] 12:[13,17] 13:[12,14] 14:[16,13]"
          " 15:[] 16:[10,8,9,16,16,11,14,17] 17:[16,12] 18:[1] 19:[1])");
    }
    {
      ostringstream oss;
      oss << b.f;
      assert(oss.str() == "Graph(n=20;"
          " 0:[2,8] 1:[18,19] 2:[3] 3:[4] 4:[]"
          " 5:[] 6:[] 7:[6] 8:[7,9] 9:[10]"
          " 10:[16] 11:[] 12:[17] 13:[12] 14:[13]"
          " 15:[] 16:[11,14] 17:[] 18:[] 19:[])");
    }
    {
      ostringstream oss;
      oss << b.gg;
      assert(oss.str() == "Graph(n=28;"
          " 0:[20,25] 1:[26,27] 2:[20] 3:[20] 4:[20]"
          " 5:[] 6:[21] 7:[21] 8:[21,24,25] 9:[24]"
          " 10:[24] 11:[22] 12:[23] 13:[23] 14:[23]"
          " 15:[] 16:[22,23,24] 17:[23] 18:[26] 19:[27]"
          " 20:[4,3,2,0] 21:[6,7,8] 22:[11,16] 23:[17,12,13,14,16] 24:[16,10,9,8]"
          " 25:[8,0] 26:[18,1] 27:[19,1])");
    }
    assert(b.isArt(0));
    assert(b.isArt(1));
    assert(!b.isArt(2));
    assert(!b.isArt(3));
    assert(!b.isArt(4));
    assert(!b.isArt(5));
    assert(!b.isArt(6));
    assert(!b.isArt(7));
    assert(b.isArt(8));
    assert(!b.isArt(9));
    assert(!b.isArt(10));
    assert(!b.isArt(11));
    assert(!b.isArt(12));
    assert(!b.isArt(13));
    assert(!b.isArt(14));
    assert(!b.isArt(15));
    assert(b.isArt(16));
    assert(!b.isArt(17));
    assert(!b.isArt(18));
    assert(!b.isArt(19));
    test_dive(b);
    test_isStillReachable(b);
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
