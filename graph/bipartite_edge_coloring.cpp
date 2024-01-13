#include <assert.h>
#include <algorithm>
#include <queue>
#include <utility>
#include <vector>

using std::max;
using std::pair;
using std::priority_queue;
using std::vector;

// !!!Modifies ns and edges!!!
// n: modified regular bipartite graph
// d := max degree = edge chromatic number
// iss[c]: edges of color c \in [0, d)
// colors[i]: color of edge i
struct BipartiteEdgeColoring {
  int ns[2];
  vector<pair<int, int>> edges;
  int n;
  int d;
  vector<int> colors;
  vector<vector<int>> iss;
  BipartiteEdgeColoring() {}
  BipartiteEdgeColoring(int n0, int n1) : ns{n0, n1}, edges() {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < ns[0]);
    assert(0 <= v); assert(v < ns[1]);
    edges.emplace_back(u, v);
  }
  void run() {
    const int m = edges.size();
    vector<int> deg[2];
    for (int s = 0; s < 2; ++s) deg[s].assign(ns[s], 0);
    for (const auto &edge : edges) {
      ++deg[0][edge.first];
      ++deg[1][edge.second];
    }
    d = 0;
    for (int s = 0; s < 2; ++s) for (int u = 0; u < ns[s]; ++u) if (d < deg[s][u]) d = deg[s][u];
    // Merge vertices of small degree.
    for (int s = 0; s < 2; ++s) {
      priority_queue<pair<int, int>, vector<pair<int, int>>, std::greater<pair<int, int>>> que;
      par.resize(ns[s]);
      for (int u = 0; u < ns[s]; ++u) que.emplace(deg[s][u], par[u] = u);
      for (; ; ) {
        if (!que.size()) break;
        const auto p0 = que.top(); que.pop();
        if (!que.size()) break;
        const auto p1 = que.top(); que.pop();
        if (p0.first + p1.first > d) break;
        par[p0.second] = p1.second;
        que.emplace(p0.first + p1.first, p1.second);
      }
      int nn = 0;
      vector<int> ids(ns[s], -1);
      for (int u = 0; u < ns[s]; ++u) if (par[u] == u) ids[u] = nn++;
      ns[s] = nn;
      if (s == 0) {
        for (auto &edge : edges) edge.first = ids[root(edge.first)];
      } else {
        for (auto &edge : edges) edge.second = ids[root(edge.second)];
      }
    }
    // Add edges to make the graph d-regular.
    n = max(ns[0], ns[1]);
    for (int s = 0; s < 2; ++s) deg[s].assign(n, 0);
    for (const auto &edge : edges) {
      ++deg[0][edge.first];
      ++deg[1][edge.second];
    }
    for (int u = 0, v = 0; ; ) {
      for (; u < n && deg[0][u] >= d; ++u) {}
      for (; v < n && deg[1][v] >= d; ++v) {}
      if (u == n && v == n) break;
      edges.emplace_back(u, v);
      ++deg[0][u];
      ++deg[1][v];
    }
    iss.clear();
    vector<int> is(n * d);
    for (int i = 0; i < n * d; ++i) is[i] = i;
    rec(is);
    // Remove added edges.
    colors.assign(m, -1);
    for (int k = 0; k < d; ++k) {
      iss[k].erase(std::lower_bound(iss[k].begin(), iss[k].end(), m), iss[k].end());
      for (const int i : iss[k]) colors[i] = k;
    }
  }
  vector<int> par;
  int root(int u) {
    return (par[u] == u) ? u : (par[u] = root(par[u]));
  }
  // is: k-regular
  void rec(vector<int> is) {
    if (!is.size()) return;
    const int k = is.size() / n;
    if (k == 1) {
      std::sort(is.begin(), is.end());
      iss.push_back(is);
    } else if (k % 2 != 0) {
      if (iss.size()) {
        is.insert(is.end(), iss.back().begin(), iss.back().end());
        iss.pop_back();
        rec(is);
      } else {
        // Add (2^e - k) bad matchings to find a perfect matching.
        const int e = (31 - __builtin_clz(k)) + 1;
        vector<int> ma(n);
        for (int u = 0; u < n; ++u) ma[u] = ~u;
        for (; ; ) {
          auto js = is;
          for (const int j : ma) for (int l = 0; l < (1 << e) - k; ++l) js.push_back(j);
          for (int f = e; --f >= 0; ) {
            const auto jss = euler(js);
            int numBads[2] = {};
            for (int s = 0; s < 2; ++s) for (const int i : jss[s]) if (i < 0) ++numBads[s];
            js = jss[(numBads[0] <= numBads[1]) ? 0 : 1];
          }
          ma.swap(js);
          bool good = true;
          for (const int j : ma) if (j < 0) {
            good = false;
            break;
          }
          if (good) break;
        }
        std::sort(ma.begin(), ma.end());
        iss.push_back(ma);
        std::sort(is.begin(), is.end());
        vector<int> iis;
        auto it = ma.begin();
        for (const int i : is) {
          for (; it != ma.end() && *it < i; ++it) {}
          if (!(it != ma.end() && *it == i)) iis.push_back(i);
        }
        rec(iis);
      }
    } else {
      const auto jss = euler(is);
      for (int s = 0; s < 2; ++s) rec(jss[s]);
    }
  }
  // Take Eulerian circuit and take edges alternately.
  vector<vector<int>> euler(const vector<int> &is) {
    const int k = is.size() / n;
    vector<int> pt(n + n);
    for (int u = 0; u < n + n; ++u) pt[u] = u * k;
    vector<pair<int, int>> xvs((n + n) * k);
    for (int x = 0; x < n * k; ++x) {
      const int i = is[x];
      int u, v;
      if (i >= 0) {
        u = edges[i].first;
        v = n + edges[i].second;
      } else {
        u = ~i;
        v = n + ~i;
      }
      xvs[pt[u]++] = std::make_pair(x, v);
      xvs[pt[v]++] = std::make_pair(x, u);
    }
    vector<int> used(n * k, 0);
    int y = 0;
    vector<vector<int>> jss(2, vector<int>(n * (k / 2)));
    vector<int> stack;
    for (int u0 = 0; u0 < n; ++u0) {
      for (stack.push_back(u0); stack.size(); ) {
        const int u = stack.back();
        if (pt[u] > u * k) {
          --pt[u];
          const int x = xvs[pt[u]].first;
          const int v = xvs[pt[u]].second;
          if (!used[x]) {
            used[x] = 1;
            jss[y & 1][y >> 1] = is[x];
            ++y;
            stack.push_back(v);
          }
        } else {
          stack.pop_back();
        }
      }
    }
    return jss;
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <iostream>
#include <set>

using std::cerr;
using std::endl;
using std::set;
using std::swap;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void check(int n0, int n1, const vector<pair<int, int>> &edges) {
  BipartiteEdgeColoring bec(n0, n1);
  for (const auto &edge : edges) bec.ae(edge.first, edge.second);
  bec.run();
  const int m = edges.size();
  vector<int> deg0(n0, 0), deg1(n1, 0);
  for (const auto &edge : edges) {
    ++deg0[edge.first];
    ++deg1[edge.second];
  }
  int maxD = 0;
  for (int u = 0; u < n0; ++u) if (maxD < deg0[u]) maxD = deg0[u];
  for (int v = 0; v < n1; ++v) if (maxD < deg1[v]) maxD = deg1[v];
  assert(bec.d == maxD);
  assert(static_cast<int>(bec.iss.size()) == maxD);
  assert(static_cast<int>(bec.colors.size()) == m);
  for (int k = 0; k < maxD; ++k) {
    set<int> us, vs;
    for (const int i : bec.iss[k]) {
      assert(0 <= i); assert(i < m);
      assert(bec.colors[i] == k);
      assert(us.insert(edges[i].first).second);
      assert(vs.insert(edges[i].second).second);
    }
  }
}
void unittest() {
  for (int n0 = 0; n0 <= 4; ++n0) for (int n1 = 0; n1 <= 4; ++n1) {
    for (int p = 0; p < 1 << (n0 * n1); ++p) {
      vector<pair<int, int>> edges;
      for (int u = 0; u < n0; ++u) for (int v = 0; v < n1; ++v) if (p >> (u * n1 + v) & 1) {
        edges.emplace_back(u, v);
      }
      check(n0, n1, edges);
    }
  }
  constexpr int MAX_N = 100;
  for (int caseId = 0; caseId < 100; ++caseId) {
    const int n0 = xrand() % (MAX_N + 1);
    const int n1 = xrand() % (MAX_N + 1);
    const int m = xrand() % (2 * n0 * n1 + 1);
    vector<pair<int, int>> edges(m);
    for (int i = 0; i < m; ++i) {
      edges[i].first = xrand() % n0;
      edges[i].second = xrand() % n1;
    }
    check(n0, n1, edges);
  }
  for (int caseId = 0; caseId < 100; ++caseId) {
    const int n = xrand() % (MAX_N + 1);
    const int d = xrand() % (2 * n + 1);
    vector<int> us(n * d), vs(n * d);
    for (int u = 0; u < n; ++u) for (int k = 0; k < d; ++k) us[u * d + k] = vs[u * d + k] = u;
    for (int i = 0; i < n * d; ++i) swap(us[xrand() % (i + 1)], us[i]);
    for (int i = 0; i < n * d; ++i) swap(vs[xrand() % (i + 1)], vs[i]);
    vector<pair<int, int>> edges(n * d);
    for (int i = 0; i < n * d; ++i) edges[i] = std::make_pair(us[i], vs[i]);
    check(n, n, edges);
  }
}

// https://judge.yosupo.jp/problem/bipartite_edge_coloring
void yosupo_bipartite_edge_coloring() {
  for (int L, R, M; ~scanf("%d%d%d", &L, &R, &M); ) {
    BipartiteEdgeColoring bec(L, R);
    for (int i = 0; i < M; ++i) {
      int a, b;
      scanf("%d%d", &a, &b);
      bec.ae(a, b);
    }
    bec.run();
    printf("%d\n", bec.d);
    for (int i = 0; i < M; ++i) {
      printf("%d\n", bec.colors[i]);
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupo_bipartite_edge_coloring();
  return 0;
}
