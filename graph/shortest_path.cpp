#include <assert.h>
#include <functional>
#include <queue>
#include <utility>
#include <vector>

using std::pair;
using std::priority_queue;
using std::vector;

// undirected graph, positive weight
template <class Cost> struct ShortestPathReplacement {
  int n, m;
  vector<int> as, bs;
  vector<Cost> cs;
  vector<vector<int>> g;

  ShortestPathReplacement() {}
  ShortestPathReplacement(int n_) : n(n_), m(0) {
    assert(0 <= n_);
    g.assign(n, {});
  }
  void ae(int u, int v, Cost c) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    assert(0 < c);
    as.push_back(u);
    bs.push_back(v);
    cs.push_back(c);
    g[u].push_back(m);
    g[v].push_back(m);
    ++m;
  }

  struct Tree {
    // -1 if unreachable
    vector<Cost> dist;
    vector<int> parV, parE;
    // increasing order of dist
    vector<int> us;
  };
  Tree shortest(int s) const {
    priority_queue<pair<Cost, int>, vector<pair<Cost, int>>, std::greater<pair<Cost, int>>> que;
    Tree tree;
    auto &dist = tree.dist; dist.assign(n, -1);
    auto &parV = tree.parV; parV.assign(n, -1);
    auto &parE = tree.parE; parE.assign(n, -1);
    auto &us = tree.us;
    que.emplace(dist[s] = 0, s);
    for (; que.size(); ) {
      const Cost c = que.top().first;
      const int u = que.top().second;
      que.pop();
      if (dist[u] == c) {
        us.push_back(u);
        for (const int i : g[u]) {
          const Cost cc = c + cs[i];
          const int v = as[i] ^ bs[i] ^ u;
          if (dist[v] < 0 || dist[v] > cc) {
            que.emplace(dist[v] = cc, v);
            parV[v] = u;
            parE[v] = i;
          }
        }
      }
    }
    return tree;
  }

  // shortest path trees from s, to t
  Tree treeS, treeT;
  // s-t shortest path
  int pathLen;
  vector<int> pathV, pathE;
  // cost of s-t shortest path when edge i is deleted (-1 if unreachable)
  vector<Cost> run(int s, int t) {
    treeS = shortest(s);
    treeT = shortest(t);
    if (treeS.dist[t] < 0) {
      pathLen = -1;
      pathV = {};
      pathE = {};
      return vector<Cost>(m, -1);
    }
    if (s == t) {
      pathLen = 0;
      pathV = {s};
      pathE = {};
      return vector<Cost>(m, 0);
    }
    pathV.clear();
    pathE.clear();
    for (int u = s; ; u = treeT.parV[u]) {
      pathV.push_back(u);
      if (u == t) break;
      pathE.push_back(treeT.parE[u]);
    }
    pathLen = pathE.size();
    // fix treeS to contain the path
    for (int k = 0; k < pathLen; ++k) {
      treeS.parV[pathV[k + 1]] = pathV[k];
      treeS.parE[pathV[k + 1]] = pathE[k];
    }
    vector<char> onV(n, 0), onE(m, 0);
    for (int k = 0; k <= pathLen; ++k) onV[pathV[k]] = 1;
    for (int k = 0; k < pathLen; ++k) onE[pathE[k]] = 1;
    vector<int> ls(n, pathLen), rs(n, 0);
    for (int k = 0; k <= pathLen; ++k) ls[pathV[k]] = rs[pathV[k]] = k;
    for (const int u : treeS.us) if (!onV[u]) ls[u] = ls[treeS.parV[u]];
    for (const int u : treeT.us) if (!onV[u]) rs[u] = rs[treeT.parV[u]];
    vector<vector<Cost>> candL(pathLen + 1), candR(pathLen + 1);
    auto addCand = [&](int u, int v, Cost c) -> void {
      if (ls[u] < rs[v]) {
        c += treeS.dist[u] + treeT.dist[v];
        candL[ls[u]].push_back(c);
        candR[rs[v]].push_back(c);
      }
    };
    for (int i = 0; i < m; ++i) if (!onE[i]) {
      addCand(as[i], bs[i], cs[i]);
      addCand(bs[i], as[i], cs[i]);
    }
    priority_queue<Cost, vector<Cost>, std::greater<Cost>> queL, queR;
    vector<Cost> ans(m, treeS.dist[t]);
    for (int k = 0; k < pathLen; ++k) {
      for (const Cost c : candL[k]) queL.push(c);
      for (; queL.size() && queR.size() && queL.top() == queR.top(); queL.pop(), queR.pop()) {}
      ans[pathE[k]] = queL.size() ? queL.top() : -1;
      for (const Cost c : candR[k + 1]) queR.push(c);
    }
    return ans;
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <algorithm>
#include <iostream>

using std::cerr;
using std::endl;
using std::min;

void unittest() {
  // TODO
}

// https://codeforces.com/contest/1163/problem/F
void codeforces1163F() {
  constexpr long long INF = 1001001001001001001LL;
  auto cost = [&](long long c) -> long long {
    return (c >= 0) ? c : INF;
  };
  int N, M, Q;
  for (; ~scanf("%d%d%d", &N, &M, &Q); ) {
    ShortestPathReplacement<long long> spr(N);
    for (int i = 0; i < M; ++i) {
      int u, v;
      long long c;
      scanf("%d%d%lld", &u, &v, &c);
      --u;
      --v;
      spr.ae(u, v, c);
    }
    const vector<long long> replacements = spr.run(0, N - 1);
    for (int q = 0; q < Q; ++q) {
      int i;
      long long c;
      scanf("%d%lld", &i, &c);
      --i;
      const long long ans = min({
        cost(replacements[i]),
        cost(spr.treeS.dist[spr.as[i]]) + c + cost(spr.treeT.dist[spr.bs[i]]),
        cost(spr.treeS.dist[spr.bs[i]]) + c + cost(spr.treeT.dist[spr.as[i]]),
      });
      printf("%lld\n", ans);
    }
  }
}

// https://atcoder.jp/contests/abc375/tasks/abc375_g
void abc375_g() {
  int N, M;
  for (; ~scanf("%d%d", &N, &M); ) {
    ShortestPathReplacement<long long> spr(N);
    for (int i = 0; i < M; ++i) {
      int u, v;
      long long c;
      scanf("%d%d%lld", &u, &v, &c);
      --u;
      --v;
      spr.ae(u, v, c);
    }
    const vector<long long> replacements = spr.run(0, N - 1);
    for (int i = 0; i < M; ++i) {
      puts((spr.treeS.dist[N - 1] != replacements[i]) ? "Yes" : "No");
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // codeforces1163F();
  // abc375_g();
  return 0;
}
