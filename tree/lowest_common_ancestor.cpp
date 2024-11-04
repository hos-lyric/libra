#include <assert.h>
#include <utility>
#include <vector>

using std::swap;
using std::vector;

// build: O(n log(n)) time/space
// operator(): O(1) time
struct Lca {
  int n, rt;
  vector<vector<int>> graph;
  vector<int> par, dep, su;
  int usLen;
  vector<int> us;
  vector<int> buffer;
  vector<int *> mn;

  Lca() : n(0), rt(-1), usLen(0) {}
  explicit Lca(int n_) : n(n_), rt(-1), graph(n), usLen(0) {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    graph[u].push_back(v);
    graph[v].push_back(u);
  }

  void dfs(int u, int p) {
    us[su[u] = usLen++] = u;
    for (const int v : graph[u]) if (p != v) {
      par[v] = u;
      dep[v] = dep[u] + 1;
      dfs(v, u);
      us[usLen++] = u;
    }
  }
  void build(int rt_) {
    assert(0 <= rt_); assert(rt_ < n);
    rt = rt_;
    par.assign(n, -1);
    dep.assign(n, -1);
    su.assign(n, -1);
    usLen = 0;
    us.assign(2 * n - 1, -1);
    dep[rt] = 0;
    dfs(rt, -1);
    assert(usLen == 2 * n - 1);
    const int l = (31 - __builtin_clz(usLen)) + 1;
    buffer.resize(l * usLen);
    mn.resize(l);
    for (int e = 0; e < l; ++e) mn[e] = buffer.data() + e * usLen;
    for (int j = 0; j < usLen; ++j) mn[0][j] = us[j];
    for (int e = 0; e < l - 1; ++e) for (int i = 0; i + (1 << (e + 1)) <= usLen; ++i) {
      mn[e + 1][i] = shallower(mn[e][i], mn[e][i + (1 << e)]);
    }
  }

  int shallower(int u, int v) const {
    return (dep[u] <= dep[v]) ? u : v;
  }
  int operator()(int u, int v) const {
    int j0 = su[u], j1 = su[v];
    if (j0 > j1) swap(j0, j1);
    ++j1;
    const int e = 31 - __builtin_clz(j1 - j0);
    return shallower(mn[e][j0], mn[e][j1 - (1 << e)]);
  }
  int dist(int u, int v) const {
    return dep[u] + dep[v] - 2 * dep[operator()(u, v)];
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <iostream>
#include <random>

using std::cerr;
using std::endl;
using std::mt19937_64;

void unittest() {
  for (int n = 1; n <= 50; ++n) for (int seed = 0; seed < 10; ++seed) {
    mt19937_64 rng(seed);
    vector<vector<int>> dist(n, vector<int>(n, n));
    for (int u = 0; u < n; ++u) dist[u][u] = 0;
    Lca lca(n);
    for (int u = 1; u < n; ++u) {
      const int p = rng() % u;
      dist[p][u] = dist[u][p] = 1;
      lca.ae(p, u);
    }
    for (int w = 0; w < n; ++w) for (int u = 0; u < n; ++u) for (int v = 0; v < n; ++v) {
      if (dist[u][v] > dist[u][w] + dist[w][v]) dist[u][v] = dist[u][w] + dist[w][v];
    }
    vector<int> rs(n);
    for (int r = 0; r < n; ++r) swap(rs[rng() % (r + 1)], rs[r] = r);
    for (const int r : rs) {
      lca.build(r);
      for (int u = 0; u < n; ++u) for (int v = 0; v < n; ++v) {
        int l = r;
        for (int w = 0; w < n; ++w) if (dist[r][u] == dist[r][w] + dist[w][u] && dist[r][v] == dist[r][w] + dist[w][v]) {
          if (dist[r][l] < dist[r][w]) l = w;
        }
        assert(lca(u, v) == l);
      }
    }
  }
}

// https://judge.yosupo.jp/problem/lca
void yosupo_lca() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    Lca lca(N);
    for (int u = 1; u < N; ++u) {
      int p;
      scanf("%d", &p);
      lca.ae(p, u);
    }
    lca.build(0);
    for (int q = 0; q < Q; ++q) {
      int u, v;
      scanf("%d%d", &u, &v);
      const int l = lca(u, v);
      printf("%d\n", l);
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupo_lca();
  return 0;
}
