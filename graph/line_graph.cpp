#include <assert.h>
#include <utility>
#include <vector>

using std::make_pair;
using std::pair;
using std::vector;

// Finds a simple undirected graph G for given simple line graph L(G).
// Adds edge of G one by one, possibly selecting K_3 or K_{1,3} at 3 edges.
//   G does not contain isolated points.
//   Components of G of size >= 5 has 1:1 correspondence between isomorphisms.
//   linear time
struct InvLineGraph {
  // m = |E(G)| = |V(L(G))|
  int m;
  vector<vector<int>> lg;
  InvLineGraph() {}
  InvLineGraph(int m_) : m(m_), lg(m) {}
  void ae(int i, int j) {
    assert(0 <= i); assert(i < m);
    assert(0 <= j); assert(j < m);
    assert(i != j);
    lg[i].push_back(j);
    lg[j].push_back(i);
  }

  // n = |V(G)| <= 2 m
  int n;
  vector<pair<int, int>> es;
  bool run(bool preferK13) {
    n = 0;
    es.assign(m, make_pair(-1, -1));
    deg.assign(2*m, 0);
    cnt.assign(2*m, 0);
    // BFS on L(G)
    vector<int> ks(m, -1);
    for (int i0 = 0; i0 < m; ++i0) if (!~ks[i0]) {
      ks[i0] = 0;
      is = {i0};
      jss.clear();
      for (int k = 0; k < (int)is.size(); ++k) {
        const int i = is[k];
        jss.emplace_back();
        for (const int j : lg[i]) {
          if (~ks[j]) {
            if (ks[j] < k) jss[k].push_back(j);
          } else {
            ks[j] = is.size();
            is.push_back(j);
          }
        }
      }
      if (is.size() == 3 && jss[2].size() == 2) {
        if (preferK13) {
          const int u0 = n++;
          const int u1 = n++;
          const int u2 = n++;
          const int u3 = n++;
          es[is[0]] = make_pair(u0, u1);
          es[is[1]] = make_pair(u0, u2);
          es[is[2]] = make_pair(u0, u3);
        } else {
          const int u0 = n++;
          const int u1 = n++;
          const int u2 = n++;
          es[is[0]] = make_pair(u0, u1);
          es[is[1]] = make_pair(u0, u2);
          es[is[2]] = make_pair(u1, u2);
        }
      } else {
        const int u0 = n++;
        const int u1 = n++;
        es[is[0]] = make_pair(u0, u1);
        ++deg[u0];
        ++deg[u1];
        if (!rec(1)) {
          n = -1;
          es.clear();
          return false;
        }
      }
    }
    return true;
  }

  vector<int> deg, cnt;
  vector<int> is;
  vector<vector<int>> jss;
  // unique call for k >= 5
  bool rec(int k) {
    if (k == (int)is.size()) return true;
    const auto &js = jss[k];
    const int jsLen = js.size();
    for (const int j : js) cnt[es[j].first] = cnt[es[j].second] = 0;
    for (const int j : js) { ++cnt[es[j].first]; ++cnt[es[j].second]; }
    vector<pair<int, int>> cands;
    for (const int u : {es[js[0]].first, es[js[0]].second}) if (deg[u] == cnt[u]) {
      if (jsLen == cnt[u]) {
        cands.emplace_back(u, n);
      } else {
        for (int x = 1; x < jsLen; ++x) if (!(u == es[js[x]].first || u == es[js[x]].second)) {
          // (jsLen == cnt[u] + cnt[v]) to make sure that edge uv is not used
          for (const int v : {es[js[x]].first, es[js[x]].second}) if (deg[v] == cnt[v] && jsLen == cnt[u] + cnt[v]) {
            bool ok = true;
            for (int y = x + 1; y < jsLen; ++y) if (!(u == es[js[y]].first || u == es[js[y]].second || v == es[js[y]].first || v == es[js[y]].second)) {
              ok = false;
              break;
            }
            if (ok) cands.emplace_back(u, v);
          }
          break;
        }
      }
    }
    for (const auto &e : cands) {
      es[is[k]] = e;
      ++deg[e.first];
      ++deg[e.second];
      if (e.second == n) {
        ++n;
        if (rec(k + 1)) return true;
        --n;
      } else {
        if (rec(k + 1)) return true;
      }
      --deg[e.first];
      --deg[e.second];
    }
    return false;
  }
};  // InvLineGraph

////////////////////////////////////////////////////////////////////////////////

#include <algorithm>
#include <iostream>

using std::cerr;
using std::endl;

void unittest() {
  // K_2 -> K_1
  {
    InvLineGraph ilg(4);
    assert(ilg.run(false));
    assert(ilg.n == 8);
    assert(ilg.es == (vector<pair<int, int>>{{0, 1}, {2, 3}, {4, 5}, {6, 7}}));
    assert(ilg.run(true));
    assert(ilg.n == 8);
    assert(ilg.es == (vector<pair<int, int>>{{0, 1}, {2, 3}, {4, 5}, {6, 7}}));
  }
  // K_3, K_{1,3} -> K_3
  {
    InvLineGraph ilg(3);
    ilg.ae(0, 1);
    ilg.ae(0, 2);
    ilg.ae(1, 2);
    assert(ilg.run(false));
    assert(ilg.n == 3);
    assert(ilg.es == (vector<pair<int, int>>{{0, 1}, {0, 2}, {1, 2}}));
    ilg.run(true);
    assert(ilg.n == 4);
    assert(ilg.es == (vector<pair<int, int>>{{0, 1}, {0, 2}, {0, 3}}));
  }
  // -> K_{1,3}
  {
    InvLineGraph ilg(4);
    ilg.ae(0, 1);
    ilg.ae(0, 2);
    ilg.ae(0, 3);
    assert(!ilg.run(false));
    assert(!ilg.run(true));
  }
  // TODO: more unittests
}

// https://qoj.ac/contest/1010/problem/4818
void qoj4818(bool preferK13) {
  int numCases;
  for (; ~scanf("%d", &numCases); ) {
    for (int caseId = 1; caseId <= numCases; ++caseId) {
      int N, M;
      scanf("%d%d", &N, &M);
      vector<int> A(M), B(M);
      for (int i = 0; i < M; ++i) {
        scanf("%d%d", &A[i], &B[i]);
        --A[i];
        --B[i];
      }
      InvLineGraph ilg(N);
      for (int i = 0; i < M; ++i) ilg.ae(A[i], B[i]);
      if (ilg.run(preferK13)) {
        puts("Yes");
        printf("%d %d\n", ilg.n, N);
        for (int u = 0; u < N; ++u) printf("%d %d\n", ilg.es[u].first + 1, ilg.es[u].second + 1);
      } else {
        puts("No");
      }
    }
  }
}

// https://qoj.ac/contest/1742/problem/11723
// Multi-edges are allowed in G: Makes closed neighborhoods distinct.
void qoj11723(bool preferK13) {
  int N, M;
  for (; ~scanf("%d%d", &N, &M); ) {
    vector<int> A(M), B(M);
    for (int i = 0; i < M; ++i) {
      scanf("%d%d", &A[i], &B[i]);
      --A[i];
      --B[i];
    }
    vector<pair<vector<int>, int>> lg(N);
    for (int u = 0; u < N; ++u) lg[u] = make_pair(vector<int>{u}, u);
    for (int i = 0; i < M; ++i) {
      lg[A[i]].first.push_back(B[i]);
      lg[B[i]].first.push_back(A[i]);
    }
    for (int u = 0; u < N; ++u) std::sort(lg[u].first.begin(), lg[u].first.end());
    for (int u = 0; u < N; ++u){for(const int v:lg[u].first)cerr<<v<<" ";cerr<<endl;}
    std::sort(lg.begin(), lg.end());
    int n = 0;
    vector<int> on(N, 0), ids(N, -1);
    for (int j = 0, k = 0; j < N; j = k) {
      const int id = n++;
      on[lg[j].second] = 1;
      for (; k < N && lg[j].first == lg[k].first; ++k) ids[lg[k].second] = id;
    }
    InvLineGraph ilg(n);
    for (int i = 0; i < M; ++i) if (on[A[i]] && on[B[i]]) ilg.ae(ids[A[i]], ids[B[i]]);
    if (ilg.run(preferK13)) {
      puts("Yes");
      for (int u = 0; u < N; ++u) printf("%d %d\n", ilg.es[ids[u]].first + 1, ilg.es[ids[u]].second + 1);
    } else {
      puts("No");
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
//  qoj4818(false);
//  qoj4818(true);
//  qoj11723(false);
//  qoj11723(true);
  return 0;
}
