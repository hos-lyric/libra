#include <assert.h>
#include <utility>
#include <vector>

using std::pair;
using std::vector;

// TODO: edge ID
// TODO: test lowlink

// gg: bipartite graph between {vertex} and {biconnected component}
//   (|gg| - n) biconnected components
//   isolated point: not regarded as biconnected component (==> isolated in gg)
// f: DFS out-forest
// ess: edges in biconnected component
//   (u, v) with dis[u] <= dis[v]
//   self-loop at isolated point: not included in ess
struct Biconnected {
  int n, m;
  vector<vector<int>> g, f, gg;
  vector<vector<pair<int, int>>> ess;
  vector<int> par, rs;
  int zeit;
  vector<int> dis, fin, low;

  Biconnected() {}
  explicit Biconnected(int n_) : n(n_), m(0), g(n_) {}
  void ae(int u, int v) {
    ++m;
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    g[u].push_back(v);
    if (u != v) g[v].push_back(u);
  }

  int stackVLen, stackELen;
  vector<int> stackV;
  vector<pair<int, int>> stackE;
  vector<int> cntPar;
  void dfs(int u) {
    stackV[stackVLen++] = u;
    dis[u] = low[u] = zeit++;
    for (const int v : g[u]) {
      if (par[u] == v && !cntPar[u]++) continue;
      if (~dis[v]) {
        if (dis[u] >= dis[v]) stackE[stackELen++] = std::make_pair(v, u);
        if (low[u] > dis[v]) low[u] = dis[v];
      } else {
        f[u].push_back(v);
        par[v] = u;
        rs[v] = rs[u];
        const int stackEPos = stackELen;
        stackE[stackELen++] = std::make_pair(u, v);
        dfs(v);
        if (low[u] > low[v]) low[u] = low[v];
        if (dis[u] <= low[v]) {
          const int x = gg.size();
          gg.emplace_back();
          ess.emplace_back();
          for (; ; ) {
            const int w = stackV[--stackVLen];
            gg[w].push_back(x);
            gg[x].push_back(w);
            if (w == v) break;
          }
          gg[u].push_back(x);
          gg[x].push_back(u);
          for (; stackELen > stackEPos; ) ess[x].push_back(stackE[--stackELen]);
        }
      }
    }
    fin[u] = zeit;
  }
  void build() {
    f.assign(n, {});
    gg.assign(n, {});
    ess.assign(n, {});
    par.assign(n, -1);
    rs.assign(n, -1);
    zeit = 0;
    dis.assign(n, -1);
    fin.assign(n, -1);
    low.assign(n, -1);
    stackV.resize(n);
    stackE.resize(m);
    cntPar.assign(n, 0);
    for (int u = 0; u < n; ++u) if (!~dis[u]) {
      stackVLen = stackELen = 0;
      rs[u] = u;
      dfs(u);
    }
  }

  // Returns true iff u is an articulation point
  //   <=> # of connected components increases when u is removed.
  inline bool isArt(int u) const {
    return (gg[u].size() >= 2);
  }

  // Returns w s.t. w is a child of u and a descendant of v in the DFS forest.
  // Returns -1 instead if v is not a proper descendant of u
  //   O(log(deg(u))) time
  int dive(int u, int v) const {
    if (dis[u] < dis[v] && dis[v] < fin[u]) {
      int j0 = 0, j1 = f[u].size();
      for (; j0 + 1 < j1; ) {
        const int j = (j0 + j1) / 2;
        ((dis[f[u][j]] <= dis[v]) ? j0 : j1) = j;
      }
      return f[u][j0];
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

#include <stdio.h>
#include <iostream>
#include <sstream>

using std::cerr;
using std::endl;
using std::ostringstream;

void test_dive(const Biconnected &b) {
  const int n = b.n;
  vector<vector<int>> d(n, vector<int>(n, n));
  for (int u = 0; u < n; ++u) d[u][u] = 0;
  for (int u = 0; u < n; ++u) for (const int v : b.f[u]) {
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
    for (int u = 0; u < n; ++u) for (const int v : b.g[u]) {
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
    assert(b.g == (vector<vector<int>>{}));
    assert(b.f == (vector<vector<int>>{}));
    assert(b.gg == (vector<vector<int>>{}));
    assert(b.ess == (vector<vector<pair<int, int>>>{}));
  }
  {
    Biconnected b(1);
    b.ae(0, 0);
    b.build();
    assert(b.g == (vector<vector<int>>{{0}}));
    assert(b.f == (vector<vector<int>>{{}}));
    assert(b.gg == (vector<vector<int>>{{}}));
    assert(b.ess == (vector<vector<pair<int, int>>>{{}}));
    assert(!b.isArt(0));
  }
  {
    Biconnected b(2);
    b.ae(0, 1);
    b.ae(1, 0);
    b.build();
    assert(b.g == (vector<vector<int>>{{1, 1}, {0, 0}}));
    assert(b.f == (vector<vector<int>>{{1}, {}}));
    assert(b.gg == (vector<vector<int>>{{2}, {2}, {1, 0}}));
    assert(b.ess == (vector<vector<pair<int, int>>>{{}, {}, {{0, 1}, {0, 1}}}));
    assert(!b.isArt(0));
    assert(!b.isArt(1));
    assert(b.isStillReachable(0, 1, 1));
    assert(b.isStillReachable(1, 0, 0));
  }
  {
    Biconnected b;
    b = Biconnected(5);
    b.ae(0, 1);
    b.ae(0, 2);
    b.ae(1, 2);
    b.ae(1, 3);
    b.ae(1, 4);
    b.ae(3, 4);
    b.build();
    assert(b.g == (vector<vector<int>>{{1, 2}, {0, 2, 3, 4}, {0, 1}, {1, 4}, {1, 3}}));
    assert(b.f == (vector<vector<int>>{{1}, {2, 3}, {}, {4}, {}}));
    assert(b.gg == (vector<vector<int>>{{6}, {5, 6}, {6}, {5}, {5}, {4, 3, 1}, {2, 1, 0}}));
    assert(b.ess == (vector<vector<pair<int, int>>>{{}, {}, {}, {}, {}, {{1, 4}, {3, 4}, {1, 3}}, {{0, 2}, {1, 2}, {0, 1}}}));
    assert(!b.isArt(0));
    assert(b.isArt(1));
    assert(!b.isArt(2));
    assert(!b.isArt(3));
    assert(!b.isArt(4));
    test_dive(b);
    test_isStillReachable(b);
  }
/*
0 2
0 3
0 4
2 3
3 4
1 18
1 19
0 8
6 7
7 8
8 6
8 9
9 10
10 16
16 8
8 10
9 16
16 16
11 16
12 13
14 16
16 17
12 17
13 14
*/
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
    assert(b.g == (vector<vector<int>>{
      {2, 3, 4, 8}, {18, 19}, {0, 3}, {0, 2, 4}, {0, 3},
      {}, {7, 8}, {6, 8}, {0, 7, 6, 9, 16, 10}, {8, 10, 16},
      {9, 16, 8}, {16}, {13, 17}, {12, 14}, {16, 13},
      {}, {10, 8, 9, 16, 11, 14, 17}, {16, 12}, {1}, {1},
    }));
    assert(b.f == (vector<vector<int>>{
      {2, 8}, {18, 19}, {3}, {4}, {},
      {}, {}, {6}, {7, 9}, {10},
      {16}, {}, {17}, {12}, {13},
      {}, {11, 14}, {}, {}, {},
    }));
    assert(b.gg == (vector<vector<int>>{
      {20, 25}, {26, 27}, {20}, {20}, {20},
      {}, {21}, {21}, {21, 24, 25}, {24},
      {24}, {22}, {23}, {23}, {23},
      {}, {22, 23, 24}, {23}, {26}, {27},
      {4, 3, 2, 0},
      {6, 7, 8},
      {11, 16},
      {17, 12, 13, 14, 16},
      {16, 10, 9, 8},
      {8, 0},
      {18, 1},
      {19, 1},
    }));
    assert(b.ess == (vector<vector<pair<int, int>>>{
      {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, 
      {{0, 4}, {3, 4}, {0, 3}, {2, 3}, {0, 2}},
      {{8, 6}, {7, 6}, {8, 7}},
      {{16, 11}},
      {{16, 17}, {12, 17}, {13, 12}, {14, 13}, {16, 14}},
      {{8, 10}, {16, 16}, {9, 16}, {8, 16}, {10, 16}, {9, 10}, {8, 9}},
      {{0, 8}},
      {{1, 18}},
      {{1, 19}},
    }));
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

// https://judge.yosupo.jp/problem/biconnected_components
void yosupo_biconnected_components() {
  int N, M;
  for (; ~scanf("%d%d", &N, &M); ) {
    Biconnected b(N);
    for (int i = 0; i < M; ++i) {
      int u, v;
      scanf("%d%d", &u, &v);
      b.ae(u, v);
    }
    b.build();

    // need to output isolated vertices
    int numComps = static_cast<int>(b.gg.size()) - N;
    for (int u = 0; u < N; ++u) if (b.gg[u].size() == 0) {
      ++numComps;
    }
    printf("%d\n", numComps);
    for (int x = N; x < static_cast<int>(b.gg.size()); ++x) {
      printf("%d", static_cast<int>(b.gg[x].size()));
      for (const int u : b.gg[x]) {
        printf(" %d", u);
      }
      puts("");
    }
    for (int u = 0; u < N; ++u) if (b.gg[u].size() == 0) {
      printf("1 %d\n", u);
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupo_biconnected_components();
  return 0;
}
