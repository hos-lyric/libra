#include <assert.h>
#include <vector>

using std::vector;

// shortest path query: take r: min deg
//   0  if  u = v
//   1  if  {u, v} \not\in G
//   2  if  {r, u}, {r, v} \not\in G
//   run bfs(neighbor of r) otherwise (<= sqrt(2m) times)
struct ComplementGraph {
  int n;
  vector<vector<int>> graph;
  ComplementGraph() {}
  ComplementGraph(int n_) : n(n_), graph(n) {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    graph[u].push_back(v);
    graph[v].push_back(u);
  }
  int queLen;
  vector<int> dist, par, que;
  void bfs(int src) {
    assert(0 <= src); assert(src < n);
    dist.assign(n, -1);
    par.assign(n, -1);
    queLen = 0;
    que.assign(n, -1);
    int vsLen = 0;
    vector<int> vs(n - 1);
    for (int v = 0; v < n; ++v) if (src != v) vs[vsLen++] = v;
    vector<int> on(n, -1);
    dist[src] = 0;
    que[queLen++] = src;
    for (int j = 0; j < queLen; ++j) {
      const int u = que[j];
      for (const int v : graph[u]) on[v] = u;
      int vsLenNxt = 0;
      for (int k = 0; k < vsLen; ++k) {
        const int v = vs[k];
        if (on[v] != u) {
          dist[v] = dist[u] + 1;
          par[v] = u;
          que[queLen++] = v;
        } else {
          vs[vsLenNxt++] = v;
        }
      }
      vsLen = vsLenNxt;
    }
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <string.h>
#include <iostream>

using std::cerr;
using std::endl;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void unittest() {
  constexpr int LIM_N = 100;
  int n;
  bool adj[LIM_N][LIM_N];
  auto test = [&]() -> void {
    int d[LIM_N][LIM_N];
    for (int u = 0; u < n; ++u) for (int v = 0; v < n; ++v) {
      d[u][v] = (u == v) ? 0 : adj[u][v] ? n : 1;
    }
    for (int w = 0; w < n; ++w) for (int u = 0; u < n; ++u) for (int v = 0; v < n; ++v) {
      if (d[u][v] > d[u][w] + d[w][v]) {
        d[u][v] = d[u][w] + d[w][v];
      }
    }
    for (int u = 0; u < n; ++u) for (int v = 0; v < n; ++v) {
      if (d[u][v] >= n) {
        d[u][v] = -1;
      }
    }
    ComplementGraph com(n);
    for (int u = 0; u < n; ++u) for (int v = u + 1; v < n; ++v) if (adj[u][v]) {
      com.ae(u, v);
    }
    for (int src = 0; src < n; ++src) {
      com.bfs(src);
      assert(static_cast<int>(com.dist.size()) == n);
      assert(static_cast<int>(com.par.size()) == n);
      assert(static_cast<int>(com.que.size()) == n);
      for (int u = 0; u < n; ++u) {
        assert(com.dist[u] == d[src][u]);
        if (d[src][u] >= 1) {
          assert(d[src][com.par[u]] == d[src][u] - 1);
        } else {
          assert(com.par[u] == -1);
        }
      }
      int queLenExpected = 0;
      for (int u = 0; u < n; ++u) if (d[src][u] >= 0) {
        ++queLenExpected;
      }
      assert(com.queLen == queLenExpected);
      for (int j = 1; j < queLenExpected; ++j) {
        assert(d[src][com.que[j - 1]] <= d[src][com.que[j]]);
      }
      for (int j = queLenExpected; j < n; ++j) {
        assert(com.que[j] == -1);
      }
    }
  };
  for (n = 0; n <= 6; ++n) {
    for (int p = 0; p < 1 << (n * (n - 1) / 2); ++p) {
      memset(adj, 0, sizeof(adj));
      int pp = p;
      for (int u = 0; u < n; ++u) for (int v = u + 1; v < n; ++v) {
        if (pp & 1) adj[u][v] = adj[v][u] = true;
        pp >>= 1;
      }
      test();
    }
  }
  for (n = 7; n <= LIM_N; ++n) {
    memset(adj, 0, sizeof(adj));
    for (int u = 0; u < n; ++u) for (int v = u + 1; v < n; ++v) {
      if (xrand() & 1) adj[u][v] = adj[v][u] = true;
    }
    test();
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
