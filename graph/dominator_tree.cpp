#include <assert.h>
#include <vector>

using std::vector;

// u dominates v <=> every src->v path passes u
// dominates: partial order
// idom[v] \lessdot v
//   immediate dominator
// idom[src] = -1
// idom[v] = -1 for v unreachable from src
// semi[v]: min ids[u] s.t. u->w[1]->...->w[k-1]->v, ids[w[*]] > ids[v]
//   sdom[v] = us[semi[v]]: semidominator
// us[0, usLen), ids: DFS order
// par: DFS tree
// O(|E| log |V|) time
struct DominatorTree {
  int n;
  vector<vector<int>> graph, hparg;
  vector<int> idom, semi;
  int usLen;
  vector<int> us, ids, par;
  vector<int> uf, ums;
  DominatorTree() {}
  DominatorTree(int n_) : n(n_), graph(n_), hparg(n_) {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    graph[u].push_back(v);
    hparg[v].push_back(u);
  }
  int root(int u) {
    if (uf[u] < 0) return u;
    const int r = root(uf[u]);
    if (semi[ums[u]] > semi[ums[uf[u]]]) ums[u] = ums[uf[u]];
    return uf[u] = r;
  }
  void dfs(int u) {
    us[ids[u] = usLen++] = u;
    for (const int v : graph[u]) if (!~ids[v]) {
      par[v] = u;
      dfs(v);
    }
  }
  void build(int src) {
    assert(0 <= src); assert(src < n);
    usLen = 0; us.assign(n, -1); ids.assign(n, -1); par.assign(n, -1);
    dfs(src);
    uf.assign(n, -1); ums.resize(n); semi.resize(n); 
    for (int u = 0; u < n; ++u) semi[ums[u] = u] = ids[u];
    vector<vector<int>> buckets(n);
    vector<int> ss(n, -1);
    for (int j = usLen; --j >= 1; ) {
      const int v = us[j];
      for (const int u : hparg[v]) if (~ids[u]) {
        root(u);
        if (semi[v] > semi[ums[u]]) semi[v] = semi[ums[u]];
      }
      buckets[us[semi[v]]].push_back(v);
      for (const int u : buckets[par[v]]) {
        root(u);
        ss[u] = ums[u];
      }
      buckets[par[v]].clear();
      uf[v] = par[v];
    }
    idom.assign(n, -1);
    for (int j = 1; j < usLen; ++j) {
      const int v = us[j];
      idom[v] = (semi[ss[v]] == semi[v]) ? us[semi[v]] : idom[ss[v]];
    }
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <iostream>

using std::cerr;
using std::endl;

void unittest() {
  // Lengauer, Tarjan, "A fast algorithm for finding dominators in a flowgraph"
  {
    DominatorTree dom(13);
    dom.ae(0, 3);
    dom.ae(0, 2);
    dom.ae(0, 1);
    dom.ae(1, 4);
    dom.ae(2, 5);
    dom.ae(2, 1);
    dom.ae(2, 4);
    dom.ae(3, 6);
    dom.ae(3, 7);
    dom.ae(4, 12);
    dom.ae(5, 8);
    dom.ae(6, 9);
    dom.ae(7, 9);
    dom.ae(7, 10);
    dom.ae(8, 5);
    dom.ae(8, 11);
    dom.ae(9, 11);
    dom.ae(10, 9);
    dom.ae(11, 0);
    dom.ae(11, 9);
    dom.ae(12, 8);
    dom.build(0);
    assert(dom.us == (vector<int>{0, 3, 6, 9, 11, 7, 10, 2, 5, 8, 1, 4, 12}));
    assert(dom.ids == (vector<int>{0, 10, 7, 1, 11, 8, 2, 5, 9, 3, 6, 4, 12}));
    assert(dom.par == (vector<int>{-1, 2, 0, 0, 1, 2, 3, 3, 5, 6, 7, 9, 4}));
    assert(dom.semi == (vector<int>{0, 0, 0, 0, 7, 0, 1, 1, 0, 0, 5, 0, 11}));
    assert(dom.idom == (vector<int>{-1, 0, 0, 0, 0, 0, 3, 3, 0, 0, 7, 0, 4}));
  }
  {
    for (int n = 1; n <= 4; ++n) {
      for (int p = 0; p < 1 << (n * n); ++p) {
        // reachability when removed x
        bool d[4 + 1][4][4] = {};
        for (int x = 0; x <= 4; ++x) {
          for (int u = 0; u < n; ++u) d[x][u][u] = true;
          for (int u = 0; u < n; ++u) for (int v = 0; v < n; ++v) if (p >> (u * n + v) & 1) {
            if (x != u && x != v) d[x][u][v] = true;
          }
          for (int w = 0; w < n; ++w) for (int u = 0; u < n; ++u) if (d[x][u][w]) {
            for (int v = 0; v < n; ++v) if (d[x][w][v]) d[x][u][v] = true;
          }
        }
        for (int s = 0; s < n; ++s) {
          DominatorTree dom(n);
          for (int u = 0; u < n; ++u) for (int v = 0; v < n; ++v) if (p >> (u * n + v) & 1) {
            dom.ae(u, v);
          }
          dom.build(s);
          assert(dom.idom[s] == -1);
          for (int v = 0; v < n; ++v) if (s != v) {
            if (d[n][s][v]) {
              vector<int> dominators;
              for (int u = 0; u < n; ++u) if (u != v && !d[u][s][v]) dominators.push_back(u);
              vector<int> us;
              for (const int u : dominators) {
                bool ok = true;
                for (const int w : dominators) if (u != w) ok = ok && (!d[w][s][u]);
                if (ok) us.push_back(u);
              }
              assert(us.size() == 1);
              assert(dom.idom[v] == us[0]);
            } else {
              assert(dom.idom[v] == -1);
            }
          }
        }
      }
      cerr << "[unittest] DONE n = " << n << endl;
    }
  }
}

void yosupo__dominatortree() {
  int N, M, S;
  for (; ~scanf("%d%d%d", &N, &M, &S); ) {
    DominatorTree dom(N);
    for (int i = 0; i < M; ++i) {
      int u, v;
      scanf("%d%d", &u, &v);
      dom.ae(u, v);
    }
    dom.build(S);
    
    for (int u = 0; u < N; ++u) {
      if (u) printf(" ");
      printf("%d", (u == S) ? S : dom.idom[u]);
    }
    puts("");
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupo__dominatortree();
  return 0;
}
