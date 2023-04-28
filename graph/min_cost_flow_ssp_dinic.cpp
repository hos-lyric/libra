#include <assert.h>
#include <algorithm>
#include <limits>
#include <queue>
#include <utility>
#include <vector>

using std::make_pair;
using std::min;
using std::pair;
using std::priority_queue;
using std::vector;

// Minimum cost flow by successive shortest paths.
// Assumes that there exists no negative-cost cycle.
// TODO: Check the range of intermediate values.
template <class Flow, class Cost> struct MinCostFlow {
  // Watch out when using types other than int and long long.
  static constexpr Flow FLOW_EPS = 1e-10L;
  static constexpr Flow FLOW_INF = std::numeric_limits<Flow>::max();
  static constexpr Cost COST_EPS = 1e-10L;
  static constexpr Cost COST_INF = std::numeric_limits<Cost>::max();

  int n, m;
  vector<int> ptr, nxt, zu;
  vector<Flow> capa;
  vector<Cost> cost;

  explicit MinCostFlow(int n_) : n(n_), m(0), ptr(n_, -1) {}
  void ae(int u, int v, Flow w, Cost c) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    assert(0 <= w);
    nxt.push_back(ptr[u]); zu.push_back(v); capa.push_back(w); cost.push_back( c); ptr[u] = m++;
    nxt.push_back(ptr[v]); zu.push_back(u); capa.push_back(0); cost.push_back(-c); ptr[v] = m++;
  }

  vector<Cost> pot, dist;
  vector<bool> vis;
  vector<int> see, lev, que;

  Flow augment(int u, int t, Flow limFlow) {
    if (u == t) return limFlow;
    for (int &i = see[u]; ~i; i = nxt[i]) if (capa[i] > FLOW_EPS) {
      const int v = zu[i];
      if (lev[u] < lev[v] && pot[v] + COST_EPS >= pot[u] + cost[i]) {
        const Flow f = augment(v, t, min(limFlow, capa[i]));
        if (f > FLOW_EPS) { capa[i] -= f; capa[i ^ 1] += f; return f; }
      }
    }
    return 0;
  }
  bool bfs(int s, int t) {
    for (int u = 0; u < n; ++u) { see[u] = ptr[u]; lev[u] = -1; }
    auto head = que.begin(), tail = que.begin();
    for (lev[*tail++ = s] = 0; head != tail; ) {
      const int u = *head++;
      for (int i = ptr[u]; ~i; i = nxt[i]) if (capa[i] > FLOW_EPS) {
        const int v = zu[i];
        if (!~lev[v] && pot[v] + COST_EPS >= pot[u] + cost[i]) {
          lev[*tail++ = v] = lev[u] + 1;
          if (v == t) return true;
        }
      }
    }
    return false;
  }

  // cost slopes[j] per flow when flows[j] <= flow <= flows[j + 1]
  vector<Flow> flows;
  vector<Cost> slopes;

  // Finds a shortest path from s to t in the residual graph.
  // O((n + m) log m) time.
  //   Assumes that the members above are set.
  //   The distance to a vertex might not be determined if it is >= dist[t].
  //   You can pass t = -1 to find a shortest path to each vertex.
  void shortest(int s, int t) {
    using Entry = pair<Cost, int>;
    priority_queue<Entry, vector<Entry>, std::greater<Entry>> pque;
    for (int u = 0; u < n; ++u) { dist[u] = COST_INF; vis[u] = false; }
    for (pque.emplace(dist[s] = 0, s); !pque.empty(); ) {
      const Cost c = pque.top().first;
      const int u = pque.top().second;
      pque.pop();
      if (vis[u]) continue;
      vis[u] = true;
      if (u == t) return;
      for (int i = ptr[u]; ~i; i = nxt[i]) if (capa[i] > FLOW_EPS) {
        const int v = zu[i];
        if (!vis[v]) {
          const Cost cc = c + cost[i] + pot[u] - pot[v];
          if (dist[v] > cc) pque.emplace(dist[v] = cc, v);
        }
      }
    }
  }

  // Finds a minimum cost flow from s to t of amount min{(max flow), limFlow}.
  //   Bellman-Ford takes O(n m) time, or O(m) time if there is no negative-cost
  //   edge, or cannot stop if there exists a negative-cost cycle.
  //   Dinic O(|slopes|) times.
  pair<Flow, Cost> run(int s, int t, Flow limFlow = FLOW_INF) {
    assert(0 <= s); assert(s < n);
    assert(0 <= t); assert(t < n);
    assert(s != t);
    assert(0 <= limFlow);
    pot.assign(n, 0);
    for (; ; ) {
      bool upd = false;
      for (int i = 0; i < m; ++i) if (capa[i] > FLOW_EPS) {
        const int u = zu[i ^ 1], v = zu[i];
        const Cost cc = pot[u] + cost[i];
        if (pot[v] > cc + COST_EPS) { pot[v] = cc; upd = true; }
      }
      if (!upd) break;
    }
    dist.resize(n);
    vis.resize(n);
    see.resize(n); lev.resize(n); que.resize(n);
    Flow totalFlow = 0;
    Cost totalCost = 0;
    flows.clear(); flows.push_back(0);
    slopes.clear();
    for (; totalFlow < limFlow; ) {
      shortest(s, t);
      if (!vis[t]) break;
      for (int u = 0; u < n; ++u) pot[u] += min(dist[u], dist[t]);
      Flow f;
      for (; totalFlow + FLOW_EPS < limFlow && bfs(s, t); ) {
        for (; (f = augment(s, t, limFlow - totalFlow)) > FLOW_EPS; totalFlow += f) {}
      }
      f = totalFlow - flows.back();
      totalCost += f * (pot[t] - pot[s]);
      flows.push_back(totalFlow);
      slopes.push_back(pot[t] - pot[s]);
    }
    return make_pair(totalFlow, totalCost);
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>

using std::cerr;
using std::endl;

// TODO: more tests
void unittest() {
  MinCostFlow<int, int> mcf(4);
  mcf.ae(0, 1, 2, 100);
  mcf.ae(2, 1, 3, 1);
  mcf.ae(3, 0, 3, 10);
  mcf.ae(3, 2, 2, 1000);
  mcf.ae(0, 2, 5, -10000);
  assert(mcf.run(3, 1, 4) == make_pair(4, -18867));
  assert(mcf.flows == (vector<int>{0, 3, 4}));
  assert(mcf.slopes == (vector<int>{-9989, 11100}));
}

// https://official.contest.yandex.com/opencupXXII/contest/39023/problems/C/
#include <stdio.h>
void opencupXXII_bytedance_I() {
  int N, M;
  for (; ~scanf("%d%d", &N, &M); ) {
    MinCostFlow<int, int> mcf(2 + N + N);
    mcf.ae(0, 1, N, 0);
    for (int u = 0; u < N; ++u) {
      mcf.ae(0, 2 + u, 1, 0);
      mcf.ae(2 + N + u, 1, 1, 0);
    }
    for (int i = 0; i < M; ++i) {
      int u, v, w;
      scanf("%d%d%d", &u, &v, &w);
      --u;
      --v;
      mcf.ae(2 + u, 2 + N + v, 1, -w);
    }
    mcf.run(0, 1, N);
    int pos = 0;
    int ans = 0;
    for (int f = 0; f < N; ++f) {
      for (; mcf.flows[pos + 1] <= f; ++pos) {}
      ans += -mcf.slopes[pos];
      printf("%d\n", ans);
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // opencupXXII_bytedance_I();
  return 0;
}
