#include <assert.h>
#include <vector>

using std::vector;

// TODO: isStillReachable (!!!check rs!!!) etc.
// TODO: edge ID
// TODO: test lowlink

// f: DFS forest
// l: # of 2-edge-connected components
// us[pt[i], pt[i + 1]): component i in reversed pre-order
// ids[u]: component ID
struct TwoEdgeConnected {
  int n;
  vector<vector<int>> g, f;
  int l;
  vector<int> pt;
  vector<int> us;
  vector<int> ids;

  TwoEdgeConnected() {}
  explicit TwoEdgeConnected(int n_) : n(n_), g(n_), l(0), stackLen(0), usLen(0), zeit(0) {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    g[u].push_back(v);
    g[v].push_back(u);
  }

  int stackLen, usLen;
  vector<int> stack;
  vector<int> par, rs;
  int zeit;
  vector<int> dis, fin, low;
  vector<int> cntPar;
  void dfs(int u) {
    stack[stackLen++] = u;
    dis[u] = low[u] = zeit++;
    for (const int v : g[u]) {
      if (par[u] == v && !cntPar[u]++) continue;
      if (~dis[v]) {
        if (low[u] > dis[v]) low[u] = dis[v];
      } else {
        f[u].push_back(v);
        par[v] = u;
        rs[v] = rs[u];
        dfs(v);
        if (low[u] > low[v]) low[u] = low[v];
      }
    }
    fin[u] = zeit;
    if (dis[u] == low[u]) {
      for (; ; ) {
        const int w = stack[--stackLen];
        us[usLen++] = w;
        if (w == u) break;
      }
      pt[++l] = usLen;
    }
  }
  void build() {
    f.assign(n, {});
    l = 0;
    pt.resize(n + 1);
    pt[0] = 0;
    usLen = 0;
    us.resize(n);
    stackLen = 0;
    stack.resize(n);
    par.assign(n, -1);
    rs.assign(n, -1);
    zeit = 0;
    dis.assign(n, -1);
    fin.assign(n, -1);
    low.assign(n, -1);
    cntPar.assign(n, 0);
    for (int u = 0; u < n; ++u) if (!~dis[u]) {
      rs[u] = u;
      dfs(u);
    }
    pt.resize(l + 1);
    ids.resize(n);
    for (int i = 0; i < l; ++i) for (int j = pt[i]; j < pt[i + 1]; ++j) {
      ids[us[j]] = i;
    }
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <sstream>

using std::cerr;
using std::endl;
using std::ostringstream;

void unittest() {
  {
    TwoEdgeConnected b(0);
    b.build();
    assert(b.g == (vector<vector<int>>{}));
    assert(b.f == (vector<vector<int>>{}));
    assert(b.l == 0);
    assert(b.pt == (vector<int>{0}));
    assert(b.us == (vector<int>{}));
    assert(b.ids == (vector<int>{}));
  }
  {
    TwoEdgeConnected b(1);
    b.ae(0, 0);
    b.build();
    assert(b.g == (vector<vector<int>>{{0, 0}}));
    assert(b.f == (vector<vector<int>>{{}}));
    assert(b.l == 1);
    assert(b.pt == (vector<int>{0, 1}));
    assert(b.us == (vector<int>{0}));
    assert(b.ids == (vector<int>{0}));
  }
  {
    TwoEdgeConnected b(2);
    b.ae(0, 1);
    b.build();
    assert(b.g == (vector<vector<int>>{{1}, {0}}));
    assert(b.f == (vector<vector<int>>{{1}, {}}));
    assert(b.l == 2);
    assert(b.pt == (vector<int>{0, 1, 2}));
    assert(b.us == (vector<int>{1, 0}));
    assert(b.ids == (vector<int>{1, 0}));
  }
  {
    TwoEdgeConnected b(2);
    b.ae(0, 1);
    b.ae(1, 0);
    b.build();
    assert(b.g == (vector<vector<int>>{{1, 1}, {0, 0}}));
    assert(b.f == (vector<vector<int>>{{1}, {}}));
    assert(b.l == 1);
    assert(b.pt == (vector<int>{0, 2}));
    assert(b.us == (vector<int>{1, 0}));
    assert(b.ids == (vector<int>{0, 0}));
  }
  {
    TwoEdgeConnected b;
    b = TwoEdgeConnected(6);
    b.ae(0, 1);
    b.ae(0, 2);
    b.ae(0, 3);
    b.ae(2, 3);
    b.ae(1, 4);
    b.ae(4, 5);
    b.ae(4, 5);
    b.build();
    assert(b.g == (vector<vector<int>>{{1, 2, 3}, {0, 4}, {0, 3}, {0, 2}, {1, 5, 5}, {4, 4}}));
    assert(b.f == (vector<vector<int>>{{1, 2}, {4}, {3}, {}, {5}, {}}));
    assert(b.l == 3);
    assert(b.pt == (vector<int>{0, 2, 3, 6}));
    assert(b.us == (vector<int>{5, 4, 1, 3, 2, 0}));
    assert(b.ids == (vector<int>{2, 1, 2, 2, 0, 0}));
  }
  {
    TwoEdgeConnected b(20);
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
      {}, {10, 8, 9, 16, 16, 11, 14, 17}, {16, 12}, {1}, {1},
    }));
    assert(b.f == (vector<vector<int>>{
      {2, 8}, {18, 19}, {3}, {4}, {},
      {}, {}, {6}, {7, 9}, {10},
      {16}, {}, {17}, {12}, {13},
      {}, {11, 14}, {}, {}, {},
    }));
    assert(b.l == 8);
    assert(b.pt == (vector<int>{0, 1, 11, 15, 16, 17, 18, 19, 20}));
    assert(b.us == (vector<int>{
      11, 17, 12, 13, 14, 16, 10, 9, 6, 7, 8, 4, 3, 2, 0, 18, 19, 1, 5, 15}));
    assert(b.ids == (vector<int>{
      2, 5, 2, 2, 2, 6, 1, 1, 1, 1, 1, 0, 1, 1, 1, 7, 1, 1, 3, 4}));
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
