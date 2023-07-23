#include <assert.h>
#include <algorithm>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

using std::ostream;
using std::string;
using std::swap;
using std::vector;

struct HLD {
  int n;
  // needs to be tree
  // vertex lists
  // modified in build(rt) (parent removed, heavy child first)
  vector<vector<int>> graph;
  vector<int> sz, par, dep;
  int zeit;
  vector<int> dis, fin, sid;
  // head vertex (minimum depth) in heavy path
  vector<int> head;

  HLD() : n(0), zeit(0) {}
  explicit HLD(int n_) : n(n_), graph(n), zeit(0) {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    graph[u].push_back(v);
    graph[v].push_back(u);
  }

  void dfsSz(int u) {
    sz[u] = 1;
    for (const int v : graph[u]) {
      auto it = std::find(graph[v].begin(), graph[v].end(), u);
      if (it != graph[v].end()) graph[v].erase(it);
      par[v] = u;
      dep[v] = dep[u] + 1;
      dfsSz(v);
      sz[u] += sz[v];
    }
  }
  void dfsHLD(int u) {
    dis[u] = zeit++;
    const int deg = graph[u].size();
    if (deg > 0) {
      int vm = graph[u][0];
      int jm = 0;
      for (int j = 1; j < deg; ++j) {
        const int v = graph[u][j];
        if (sz[vm] < sz[v]) {
          vm = v;
          jm = j;
        }
      }
      swap(graph[u][0], graph[u][jm]);
      head[vm] = head[u];
      dfsHLD(vm);
      for (int j = 1; j < deg; ++j) {
        const int v = graph[u][j];
        head[v] = v;
        dfsHLD(v);
      }
    }
    fin[u] = zeit;
  }
  void build(int rt) {
    assert(0 <= rt); assert(rt < n);
    sz.assign(n, 0);
    par.assign(n, -1);
    dep.assign(n, -1);
    dep[rt] = 0;
    dfsSz(rt);
    zeit = 0;
    dis.assign(n, -1);
    fin.assign(n, -1);
    head.assign(n, -1);
    head[rt] = rt;
    dfsHLD(rt);
    assert(zeit == n);
    sid.assign(n, -1);
    for (int u = 0; u < n; ++u) sid[dis[u]] = u;
  }

  friend ostream &operator<<(ostream &os, const HLD &hld) {
    const int maxDep = *max_element(hld.dep.begin(), hld.dep.end());
    vector<string> ss(2 * maxDep + 1);
    int pos = 0, maxPos = 0;
    for (int j = 0; j < hld.n; ++j) {
      const int u = hld.sid[j];
      const int d = hld.dep[u];
      if (hld.head[u] == u) {
        if (j != 0) {
          pos = maxPos + 1;
          ss[2 * d - 1].resize(pos, '-');
          ss[2 * d - 1] += '+';
        }
      } else {
        ss[2 * d - 1].resize(pos, ' ');
        ss[2 * d - 1] += '|';
      }
      ss[2 * d].resize(pos, ' ');
      ss[2 * d] += std::to_string(u);
      if (maxPos < static_cast<int>(ss[2 * d].size())) {
        maxPos = ss[2 * d].size();
      }
    }
    for (int d = 0; d <= 2 * maxDep; ++d) os << ss[d] << '\n';
    return os;
  }

  int lca(int u, int v) const {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    for (; head[u] != head[v]; ) (dis[u] > dis[v]) ? (u = par[head[u]]) : (v = par[head[v]]);
    return (dis[u] > dis[v]) ? v : u;
  }
  // TODO: jumpUp
  // TODO: jump
  // TODO: doPathUp
  // TODO: doPath
  // TODO: compress
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>

using std::cerr;
using std::endl;
using std::ostringstream;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void unittest() {
  {
    HLD hld(1);
    hld.build(0);
    {
      ostringstream oss;
      oss << hld;
      assert(oss.str() == string(R"(
0
)").substr(1));
    }
    assert(hld.graph == (vector<vector<int>>{{}}));
    assert(hld.sz == (vector<int>{1}));
    assert(hld.par == (vector<int>{-1}));
    assert(hld.dep == (vector<int>{0}));
    assert(hld.dis == (vector<int>{0}));
    assert(hld.fin == (vector<int>{1}));
    assert(hld.head == (vector<int>{0}));
    assert(hld.lca(0, 0) == 0);
  }
  {
    HLD hld(14);
    hld.ae(0, 6);
    hld.ae(0, 9);
    hld.ae(12, 0);
    hld.ae(2, 10);
    hld.ae(1, 2);
    hld.ae(7, 2);
    hld.ae(2, 4);
    hld.ae(2, 13);
    hld.ae(9, 3);
    hld.graph[11].push_back(5);  // to test the modification of graph
    hld.ae(8, 12);
    hld.ae(11, 8);
    hld.ae(7, 8);
    hld.build(8);
    {
      ostringstream oss;
      oss << hld;
      assert(oss.str() == string(R"(
8
|---------+--+
7         11 12
|         |  |
2         5  0
|--+-+-+     |--+
10 1 4 13    9  6
             |
             3
)").substr(1));
    }
    assert(hld.graph == (vector<vector<int>>{
      {9, 6}, {}, {10, 1, 4, 13}, {}, {}, {}, {}, {2}, {7, 11, 12}, {3}, {}, {5}, {0}, {}
    }));
    assert(hld.sz == (vector<int>{4, 1, 5, 1, 1, 1, 1, 6, 14, 2, 1, 2, 5, 1}));
    assert(hld.par == (vector<int>{12, 2, 7, 9, 2, 11, 0, 8, -1, 0, 2, 8, 8, 2}));
    assert(hld.dep == (vector<int>{2, 3, 2, 4, 3, 2, 3, 1, 0, 3, 3, 1, 1, 3}));
    assert(hld.dis == (vector<int>{10, 4, 2, 12, 5, 8, 13, 1, 0, 11, 3, 7, 9, 6}));
    assert(hld.fin == (vector<int>{14, 5, 7, 13, 6, 9, 14, 7, 14, 13, 4, 9, 14, 7}));
    assert(hld.head == (vector<int>{12, 1, 8, 12, 4, 11, 6, 8, 8, 12, 8, 11, 12, 13}));
    assert(hld.lca(8, 8) == 8);
    assert(hld.lca(1, 8) == 8);
    assert(hld.lca(8, 0) == 8);
    assert(hld.lca(1, 0) == 8);
    assert(hld.lca(6, 10) == 8);
    assert(hld.lca(7, 7) == 7);
    assert(hld.lca(7, 2) == 7);
    assert(hld.lca(13, 7) == 7);
    assert(hld.lca(4, 13) == 2);
    assert(hld.lca(6, 9) == 0);
    assert(hld.lca(12, 6) == 12);
  }
  {
    constexpr int NUM_CASES = 1000;
    constexpr int MAX_N = 100;
    for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
      const int N = 1 + xrand() % MAX_N;
      vector<vector<int>> dist(N, vector<int>(N, N));
      for (int u = 0; u < N; ++u) dist[u][u] = 0;
      HLD hld(N);
      for (int v = 1; v < N; ++v) {
        const int u = xrand() % v;
        dist[u][v] = 1;
        hld.ae(u, v);
      }
      for (int w = 0; w < N; ++w) for (int u = 0; u < N; ++u) for (int v = 0; v < N; ++v) {
        if (dist[u][v] > dist[u][w] + dist[w][v]) {
          dist[u][v] = dist[u][w] + dist[w][v];
        }
      }
      hld.build(0);
      for (int u = 0; u < N; ++u) {
        for (const int v : hld.graph[u]) {
          assert(hld.sz[hld.graph[u][0]] >= hld.sz[v]);
        }
      }
      for (int u = 0; u < N; ++u) for (int v = 0; v < N; ++v) {
        int l = 0;
        for (int w = 0; w < N; ++w) if (dist[w][u] < N && dist[w][v] < N) {
          if (dist[l][w] < N) {
            l = w;
          }
        }
        assert(hld.lca(u, v) == l);
      }
    }
  }
}

#include <stdio.h>

// https://judge.yosupo.jp/problem/lca
void yosupo__lca() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    HLD hld(N);
    for (int u = 1; u < N; ++u) {
      int p;
      scanf("%d", &p);
      hld.ae(p, u);
    }
    hld.build(0);
    for (int q = 0; q < Q; ++q) {
      int u, v;
      scanf("%d%d", &u, &v);
      const int l = hld.lca(u, v);
      printf("%d\n", l);
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupo__lca();
  return 0;
}
