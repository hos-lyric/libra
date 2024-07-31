// TODO: unittest

#include <assert.h>
#include <algorithm>
#include <queue>
#include <utility>
#include <vector>

using std::pair;
using std::queue;
using std::vector;

// Find max size independet set.
//   score: max size
//   on: optimal independent set (0/1)
// M0, M1: matroid
//   size(): |ground set|
//   build(on): Current independent set is given.
//   circuit(u): Returns the circuit by adding u (must contain u), or {} if still independent.
template <class M0, class M1>
pair<int, vector<int>> matroidIntersection(M0 &m0, M1 &m1) {
  const int n = m0.size();
  assert(m1.size() == n);
  vector<int> on(n, 0);
  for (; ; ) {
    m0.build(on);
    m1.build(on);
    vector<vector<int>> graph(n + 2);
    for (int u = 0; u < n; ++u) if (!on[u]) {
      const vector<int> c0 = m0.circuit(u);
      if (c0.empty()) graph[n].push_back(u);
      for (const int v : c0) if (u != v) graph[v].push_back(u);
      const vector<int> c1 = m1.circuit(u);
      if (c1.empty()) graph[u].push_back(n + 1);
      for (const int v : c1) if (u != v) graph[u].push_back(v);
    }
    queue<int> que;
    vector<int> prv(n + 2, -1);
    prv[n] = -2; que.push(n);
    for (; que.size() && !~prv[n + 1]; ) {
      const int u = que.front(); que.pop();
      for (const int v : graph[u]) {
        if (!~prv[v]) {
          prv[v] = u;
          que.push(v);
        }
      }
    }
    if (~prv[n + 1]) {
      for (int u = n + 1; (u = prv[u]) != n; ) on[u] ^= 1;
    } else {
      break;
    }
  }
  int score = 0;
  for (int u = 0; u < n; ++u) if (on[u]) ++score;
  return std::make_pair(score, on);
};

// Find max weight independet set.
//   score: max weight
//   on: optimal independent set (0/1)
// M0, M1: matroid
//   size(): |ground set|
//   build(on): Current independent set is given.
//   circuit(u): Returns the circuit by adding u (must contain u), or {} if still independent.
template <class M0, class M1, class T>
pair<T, vector<int>> matroidIntersection(M0 &m0, M1 &m1, const vector<T> &weights) {
  const int n = weights.size();
  assert(m0.size() == n);
  assert(m1.size() == n);
  for (int u = 0; u < n; ++u) assert(weights[u] >= 0);
  vector<int> on(n, 0);
  for (; ; ) {
    m0.build(on);
    m1.build(on);
    vector<vector<int>> graph(n + 2);
    for (int u = 0; u < n; ++u) if (!on[u]) {
      const vector<int> c0 = m0.circuit(u);
      if (c0.empty()) graph[n].push_back(u);
      for (const int v : c0) if (u != v) graph[v].push_back(u);
      const vector<int> c1 = m1.circuit(u);
      if (c1.empty()) graph[u].push_back(n + 1);
      for (const int v : c1) if (u != v) graph[u].push_back(v);
    }
    queue<int> que;
    vector<int> inq(n + 2, 0);
    vector<int> prv(n + 2, -1);
    vector<T> dist(n + 2, T());
    prv[n] = -2; inq[n] = 1; que.push(n);
    for (; que.size(); ) {
      const int u = que.front(); que.pop(); inq[u] = 0;
      for (const int v : graph[u]) {
        T cc = dist[u];
        if (v < n) on[v] ? (cc -= weights[v]) : (cc += weights[v]);
        if (!~prv[v] || dist[v] < cc) {
          prv[v] = u;
          dist[v] = cc;
          if (!inq[v]) { inq[v] = 1; que.push(v); }
        }
      }
    }
    if (~prv[n + 1] && dist[n + 1] > 0) {
      for (int u = n + 1; (u = prv[u]) != n; ) on[u] ^= 1;
    } else {
      break;
    }
  }
  T score = T();
  for (int u = 0; u < n; ++u) if (on[u]) score += weights[u];
  return std::make_pair(score, on);
};

// independent  <=>  forest
struct ForestMatroid {
  int n;
  vector<pair<int, int>> edges;
  ForestMatroid() {}
  ForestMatroid(int n_) : n(n_) {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    edges.emplace_back(u, v);
  }
  inline int size() const {
    return edges.size();
  }
  void build(const vector<int> &on) {
    const int m = edges.size();
    g.assign(n, {});
    for (int i = 0; i < m; ++i) if (on[i]) {
      g[edges[i].first].push_back(i);
      g[edges[i].second].push_back(i);
    }
    rs.assign(n, -1);
    pari.assign(n, -1);
    dep.assign(n, -1);
    for (int r = 0; r < n; ++r) if (!~rs[r]) dfs(r, r, -1, 0);
  }
  // i0, then tree edges from edges[i0].first to edges[i0].second
  vector<int> circuit(int i0) const {
    int u = edges[i0].first, v = edges[i0].second;
    if (rs[u] != rs[v]) return {};
    vector<int> isU, isV;
    auto upU = [&]() -> void { const int i = pari[u]; isU.push_back(i); u ^= edges[i].first ^ edges[i].second; };
    auto upV = [&]() -> void { const int i = pari[v]; isV.push_back(i); v ^= edges[i].first ^ edges[i].second; };
    for (; dep[u] > dep[v]; upU()) {}
    for (; dep[u] < dep[v]; upV()) {}
    for (; u != v; upU(), upV()) {}
    std::reverse(isV.begin(), isV.end());
    vector<int> is{i0};
    is.insert(is.end(), isU.begin(), isU.end());
    is.insert(is.end(), isV.begin(), isV.end());
    return is;
  }
  vector<vector<int>> g;
  vector<int> rs, pari, dep;
  void dfs(int r, int u, int pi, int d) {
    rs[u] = r; pari[u] = pi; dep[u] = d;
    for (const int i : g[u]) if (pi != i) {
      dfs(r, edges[i].first ^ edges[i].second ^ u, i, d + 1);
    }
  }
};

// independent  <=>  each connected component contains (<= 1) cycle
struct PseudoforestMatroid {
  int n;
  vector<pair<int, int>> edges;
  PseudoforestMatroid() {}
  PseudoforestMatroid(int n_) : n(n_) {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    edges.emplace_back(u, v);
  }
  inline int size() const {
    return edges.size();
  }
  void build(const vector<int> &on) {
    const int m = edges.size();
    g.assign(n, {});
    for (int i = 0; i < m; ++i) if (on[i]) {
      g[edges[i].first].push_back(i);
      g[edges[i].second].push_back(i);
    }
    rs.assign(n, -1);
    pari.assign(n, -1);
    dep.assign(n, -1);
    cycs.assign(n, -1);
    for (int r = 0; r < n; ++r) if (!~rs[r]) dfs(r, r, -1, 0);
  }
  vector<int> circuit(int i0) const {
    vector<int> is;
    // Add edges in the smallest subtree containing us.
    auto addSubtree = [&](vector<int> us) -> void {
      for (; ; ) {
        std::sort(us.begin(), us.end());
        us.erase(std::unique(us.begin(), us.end()), us.end());
        if (us.size() == 1) break;
        int mx = -1;
        for (const int u : us) if (mx < dep[u]) mx = dep[u];
        for (int &u : us) if (mx == dep[u]) {
          const int i = pari[u]; is.push_back(i); u ^= edges[i].first ^ edges[i].second;
        }
      }
    };
    const int u = edges[i0].first, v = edges[i0].second;
    if (rs[u] != rs[v]) {
      if (~cycs[rs[u]] && ~cycs[rs[v]]) {
        is.push_back(i0);
        is.push_back(cycs[rs[u]]);
        addSubtree({u, edges[cycs[rs[u]]].first, edges[cycs[rs[u]]].second});
        is.push_back(cycs[rs[v]]);
        addSubtree({v, edges[cycs[rs[v]]].first, edges[cycs[rs[v]]].second});
      }
    } else {
      if (~cycs[rs[u]]) {
        is.push_back(i0);
        is.push_back(cycs[rs[u]]);
        addSubtree({u, v, edges[cycs[rs[u]]].first, edges[cycs[rs[u]]].second});
      }
    }
    return is;
  }
  vector<vector<int>> g;
  vector<int> rs, pari, dep, cycs;
  void dfs(int r, int u, int pi, int d) {
    rs[u] = r; pari[u] = pi; dep[u] = d;
    for (const int i : g[u]) if (pi != i) {
      const int v = edges[i].first ^ edges[i].second ^ u;
      if (~rs[v]) {
        cycs[r] = i;
      } else {
        dfs(r, v, i, d + 1);
      }
    }
  }
};

// independent  <=>  #{ i | colors[i] = c } <= lims[c]
struct PartitionMatroid {
  int n;
  vector<int> colors;
  vector<int> lims;
  PartitionMatroid() {}
  PartitionMatroid(const vector<int> &colors_, const vector<int> &lims_)
      : n(colors_.size()), colors(colors_), lims(lims_) {}
  inline int size() const {
    return n;
  }
  void build(const vector<int> &on) {
    iss.assign(lims.size(), {});
    for (int i = 0; i < n; ++i) if (on[i]) iss[colors[i]].push_back(i);
  }
  vector<int> circuit(int i0) const {
    const int c = colors[i0];
    if (static_cast<int>(iss[c].size()) == lims[c]) {
      vector<int> is = iss[c];
      is.push_back(i0);
      return is;
    } else {
      return {};
    }
  }
  vector<vector<int>> iss;
};

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <iostream>

using std::cerr;
using std::endl;

void unittest() {
}

// https://loj.ac/p/2488
void loj2488() {
  int N, M;
  for (; ~scanf("%d%d", &N, &M); ) {
    int T0, T1;
    scanf("%d%d", &T0, &T1);
    vector<int> A0(M), B0(M), A1(M), B1(M), C(M);
    for (int i = 0; i < M; ++i) {
      scanf("%d%d%d%d%d", &A0[i], &B0[i], &A1[i], &B1[i], &C[i]);
      --A0[i];
      --B0[i];
      --A1[i];
      --B1[i];
    }
    
    pair<int, vector<int>> ans;
#define solve \
  for (int i = 0; i < M; ++i) { \
    m0.ae(A0[i], B0[i]); \
    m1.ae(A1[i], B1[i]); \
  } \
  ans = matroidIntersection(m0, m1, C); \
  {}
    if (T0 == 1) {
      if (T1 == 1) {
        ForestMatroid m0(N);
        ForestMatroid m1(N);
        solve;
      } else {
        ForestMatroid m0(N);
        PseudoforestMatroid m1(N);
        solve;
      }
    } else {
      if (T1 == 1) {
        PseudoforestMatroid m0(N);
        ForestMatroid m1(N);
        solve;
      } else {
        PseudoforestMatroid m0(N);
        PseudoforestMatroid m1(N);
        solve;
      }
    }
#undef solve
    printf("%d\n", ans.first);
  }
}

int main() {
  // unittest(); cerr << "PASSED unittest" << endl;
  loj2488();
  return 0;
}
