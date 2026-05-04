#include <assert.h>
#include <algorithm>
#include <map>
#include <queue>
#include <utility>
#include <vector>

using std::map;
using std::queue;
using std::swap;
using std::vector;

// Dfa::ac can be any int.
// Nfa::ac is cast to bool.

// n: number of states
// s: initial state
// a: alphabet size
struct Dfa {
  int n, s, a;
  vector<vector<int>> to;
  vector<int> ac;
  Dfa() : n(0), s(-1), a(0), nn(-1) {}
  Dfa(int n_, int s_, int a_) : n(n_), s(s_), a(a_), to(n, vector<int>(a, -1)), ac(n, 0), nn(-1) {}
  int addState(int acu = 0) {
    const int u = n++;
    to.emplace_back(a, -1);
    ac.push_back(acu);
    return u;
  }

  vector<vector<vector<int>>> from;
  int nn;
  vector<int> ids;
  vector<vector<int>> uss;
  Dfa minimize() {
    assert(0 <= s); assert(s < n);
    for (int u = 0; u < n; ++u) for (int e = 0; e < a; ++e) {
      assert(0 <= to[u][e]); assert(to[u][e] < n);
    }
    // BFS to find reachable states
    {
      int queLen = 0;
      vector<int> que(n);
      ids.assign(n, -1);
      ids[que[queLen++] = s] = -2;
      for (int j = 0; j < queLen; ++j) {
        const int u = que[j];
        for (int e = 0; e < a; ++e) if (!~ids[to[u][e]]) ids[que[queLen++] = to[u][e]] = -2;
      }
    }
    // reverse transitions
    from.assign(n, vector<vector<int>>(a));
    for (int u = 0; u < n; ++u) if (~ids[u]) {
      for (int e = 0; e < a; ++e) from[to[u][e]][e].push_back(u);
    }
    // separate by ac
    vector<int> acs;
    for (int u = 0; u < n; ++u) if (~ids[u]) acs.push_back(ac[u]);
    std::sort(acs.begin(), acs.end());
    acs.erase(std::unique(acs.begin(), acs.end()), acs.end());
    nn = acs.size();
    // uss as queue
    uss.assign(n, {});
    for (int u = 0; u < n; ++u) if (~ids[u]) uss[std::lower_bound(acs.begin(), acs.end(), ac[u]) - acs.begin()].push_back(u);
    {
      int xm = 0;
      for (int x = 1; x < nn; ++x) if (uss[xm].size() < uss[x].size()) xm = x;
      uss[0].swap(uss[xm]);
    }
    vector<int> where(n, -1);
    for (int x = 0; x < nn; ++x) {
      for (int i = 0; i < static_cast<int>(uss[x].size()); ++i) {
        const int u = uss[x][i];
        ids[u] = x;
        where[u] = i;
      }
    }
    {
      vector<int> ys;
      vector<vector<int>> vss(n);
      for (int x = 1; x < nn; ++x) {
        // partition by reachability to us
        const auto us = uss[x];  // copy
        // partition by reachability to uss[x]
        for (int e = 0; e < a; ++e) {
          ys.clear();
          for (const int u : us) for (const int v : from[u][e]) {
            const int y = ids[v];
            if (!vss[y].size()) ys.push_back(y);
            // move v from uss[y] to vss[y]
            where[uss[y].back()] = where[v];
            swap(uss[y].back(), uss[y][where[v]]);
            uss[y].pop_back();
            where[v] = vss[y].size();
            vss[y].push_back(v);
          }
          for (const int y : ys) {
            // O(|vss[y]|) time
            if (uss[y].size()) {
              const int z = nn++;
              uss[z].swap(vss[y]);
              if (uss[y].size() < uss[z].size()) uss[y].swap(uss[z]);
              for (const int u : uss[z]) ids[u] = z;
            } else {
              uss[y].swap(vss[y]);
            }
          }
        }
      }
    }
    uss.resize(nn);
    // to make the output unique
    for (auto &us : uss) std::sort(us.begin(), us.end());
    std::sort(uss.begin(), uss.end());
    for (int x = 0; x < nn; ++x) for (const int u : uss[x]) ids[u] = x;
    // make new DFA
    Dfa dfa(nn, ids[s], a);
    for (int x = 0; x < nn; ++x) {
      const int u = uss[x][0];
      for (int e = 0; e < a; ++e) dfa.to[x][e] = ids[to[u][e]];
      dfa.ac[x] = ac[u];
    }
    return dfa;
  }
};  // Dfa

// Checks if reachable parts are isomorphic.
bool isIsomorphic(const Dfa &dfa0, const Dfa &dfa1) {
  if (dfa0.a != dfa1.a) return false;
  const int a = dfa0.a;
  vector<int> f01(dfa0.n, -1);
  vector<int> f10(dfa1.n, -1);
  int queLen = 0;
  vector<int> que0(dfa0.n);
  vector<int> que1(dfa1.n);
  f10[f01[dfa0.s] = dfa1.s] = dfa0.s;
  que0[queLen] = dfa0.s;
  que1[queLen] = dfa1.s;
  ++queLen;
  for (int j = 0; j < queLen; ++j) {
    const int u0 = que0[j];
    const int u1 = que1[j];
    for (int e = 0; e < a; ++e) {
      const int v0 = dfa0.to[u0][e];
      const int v1 = dfa1.to[u1][e];
      if (!~f01[v0] && !~f10[v1]) {
        f10[f01[v0] = v1] = v0;
        que0[queLen] = v0;
        que1[queLen] = v1;
        ++queLen;
      } else {
        if (!~f01[v0]) return false;
        if (!~f10[v1]) return false;
        if (f10[f01[v0]] != v0) return false;
        if (f01[f10[v1]] != v1) return false;
      }
    }
  }
  for (int u0 = 0; u0 < dfa0.n; ++u0) if (~f01[u0] && dfa0.ac[u0] != dfa1.ac[f01[u0]]) return false;
  return true;
}

// n: number of states
// s: initial state
// a: alphabet size
struct Nfa {
  int n, s, a;
  vector<vector<vector<int>>> to;
  vector<vector<int>> eps;
  vector<int> ac;
  Nfa() : n(0), s(-1), a(0) {}
  Nfa(int n_, int s_, int a_) : n(n_), s(s_), a(a_), to(n, vector<vector<int>>(a)), eps(n), ac(n, 0) {}
  int addState(int acu) {
    const int u = n++;
    to.emplace_back(a);
    eps.emplace_back();
    ac.push_back(acu);
    return u;
  }
  Dfa toDfa() const {
    // BFS for eps transitions
    vector<int> que(n);
    vector<int> vis(n, -1);
    vector<vector<int>> epsed(n);
    for (int u = 0; u < n; ++u) {
      int queLen = 0;
      vis[que[queLen++] = u] = u;
      for (int j = 0; j < queLen; ++j) {
        const int v = que[j];
        for (const int w : eps[v]) if (vis[w] != u) vis[que[queLen++] = w] = u;
      }
      epsed[u] = vector<int>(que.begin(), que.begin() + queLen);
      std::sort(epsed[u].begin(), epsed[u].end());
    }
    // uss as queue
    vector<vector<int>> uss;
    map<vector<int>, int> ids;
    uss.push_back(epsed[s]);
    ids[epsed[s]] = 0;
    Dfa dfa(1, 0, a);
    for (int x = 0; x < dfa.n; ++x) {
      for (int e = 0; e < a; ++e) {
        vector<int> ws;
        for (const int u : uss[x]) for (const int v : to[u][e]) ws.insert(ws.end(), epsed[v].begin(), epsed[v].end());
        std::sort(ws.begin(), ws.end());
        ws.erase(std::unique(ws.begin(), ws.end()), ws.end());
        auto it = ids.find(ws);
        if (it != ids.end()) {
          dfa.to[x][e] = it->second;
        } else {
          uss.push_back(ws);
          const int y = dfa.addState();
          ids[ws] = dfa.to[x][e] = y;
        }
      }
    }
    // cast ac to bool
    for (int x = 0; x < dfa.n; ++x) for (const int u : uss[x]) if (ac[u]) dfa.ac[x] = 1;
    return dfa;
  }
};  // Nfa

////////////////////////////////////////////////////////////////////////////////

#include <iostream>

using std::cerr;
using std::endl;

void unittest_Dfa() {
  {
    Dfa dfa(0, 1, 1);
    dfa.addState(58);
    dfa.addState(58);
    dfa.addState(58);
    dfa.to = {{1}, {2}, {0}};
    const Dfa minDfa = dfa.minimize();
    assert(dfa.nn == 1);
    assert(dfa.ids == (vector<int>{0, 0, 0}));
    assert(dfa.uss == (vector<vector<int>>{{0, 1, 2}}));
    assert(minDfa.n == 1);
    assert(minDfa.to == (vector<vector<int>>{{0}}));
    assert(minDfa.ac == (vector<int>{58}));
  }
  {
    Dfa dfa(0, 2, 1);
    dfa.addState(2);
    dfa.addState();
    dfa.addState(1);
    dfa.to = {{1}, {2}, {0}};
    const Dfa minDfa = dfa.minimize();
    assert(dfa.nn == 3);
    assert(dfa.ids == (vector<int>{0, 1, 2}));
    assert(dfa.uss == (vector<vector<int>>{{0}, {1}, {2}}));
    assert(minDfa.n == 3);
    assert(minDfa.to == (vector<vector<int>>{{1}, {2}, {0}}));
    assert(minDfa.ac == (vector<int>{2, 0, 1}));
  }
  {
    Dfa dfa(7, 1, 2);
    dfa.to = {{1, 2}, {2, 4}, {5, 3}, {2, 6}, {1, 5}, {5, 5}, {3, 5}};
    dfa.ac[1] = dfa.ac[3] = 1;
    const Dfa minDfa = dfa.minimize();
    assert(dfa.nn == 4);
    assert(dfa.ids == (vector<int>{-1, 0, 1, 0, 2, 3, 2}));
    assert(dfa.uss == (vector<vector<int>>{{1, 3}, {2}, {4, 6}, {5}}));
    assert(minDfa.n == 4);
    assert(minDfa.s == 0);
    assert(minDfa.a == 2);
    assert(minDfa.to == (vector<vector<int>>{{1, 2}, {3, 0}, {0, 3}, {3, 3}}));
    assert(minDfa.ac == (vector<int>{1, 0, 0, 0}));
  }
  // mod (l m) in base b
  for (int b = 2; b <= 8; ++b) for (int m = 1; m <= 8; ++m) for (int l = 1; l <= 8; ++l) {
    Dfa dfa(l * m, 0, b);
    for (int u = 0; u < l * m; ++u) for (int e = 0; e < b; ++e) dfa.to[u][e] = (u * b + e) % (l * m);
    for (int u = 0; u < l * m; ++u) dfa.ac[u] = u % m;
    const Dfa minDfa = dfa.minimize();
    assert(dfa.nn == m);
    assert(static_cast<int>(dfa.ids.size()) == l * m);
    for (int u = 0; u < l * m; ++u) assert(dfa.ids[u] == u % m);
    assert(static_cast<int>(dfa.uss.size()) == m);
    for (int x = 0; x < m; ++x) {
      assert(static_cast<int>(dfa.uss[x].size()) == l);
      for (int y = 0; y < l; ++y) assert(dfa.uss[x][y] == y * m + x);
    }
    assert(minDfa.n == m);
    assert(minDfa.s == 0);
    assert(minDfa.a == b);
    assert(static_cast<int>(minDfa.to.size()) == m);
    for (int x = 0; x < m; ++x) for (int e = 0; e < b; ++e) assert(minDfa.to[x][e] == (x * b + e) % m);
    assert(static_cast<int>(minDfa.ac.size()) == m);
    for (int x = 0; x < m; ++x) assert(minDfa.ac[x] == x);
  }
  // 0 -> 1 -> ... -> N-2 -> N-1
  {
    constexpr int N = 100'000;
    Dfa dfa(N, 0, 1);
    for (int u = 0; u < N - 1; ++u) dfa.to[u][0] = u + 1;
    dfa.to[N - 1][0] = N - 1;
    dfa.ac[N - 1] = 1;
    const Dfa minDfa = dfa.minimize();
    assert(minDfa.n == N);
    assert(minDfa.s == 0);
    assert(minDfa.a == 1);
    assert(minDfa.to == dfa.to);
    assert(minDfa.ac == dfa.ac);
  }
}

void unittest_isIsomorphic() {
  Dfa dfa0(5, 0, 2);
  dfa0.to = {{1, 2}, {3, 0}, {0, 3}, {3, 3}, {2, 4}};
  dfa0.ac = {1, -1, 0, 0, 1};
  assert(isIsomorphic(dfa0, dfa0));

  Dfa dfa1(6, 3, 2);  // 0->3, 1->5, 2->0, 3->4
  dfa1.to = {{3, 4}, {2, 1}, {0, 3}, {5, 0}, {4, 4}, {4, 3}};
  dfa1.ac = {0, 0, 1, 1, 0, -1};
  assert(isIsomorphic(dfa0, dfa1));
  assert(isIsomorphic(dfa1, dfa0));

  Dfa dfa2 = dfa0;
  dfa2.a = 1;
  for (int u = 0; u < 5; ++u) dfa2.to.resize(1);
  assert(!isIsomorphic(dfa0, dfa2));
  assert(!isIsomorphic(dfa2, dfa0));

  Dfa dfa3 = dfa0;
  dfa3.to[1][0] = 4;
  assert(!isIsomorphic(dfa0, dfa3));
  assert(!isIsomorphic(dfa3, dfa0));

  Dfa dfa4 = dfa0;
  dfa4.to[1][0] = 2;
  assert(!isIsomorphic(dfa0, dfa4));
  assert(!isIsomorphic(dfa4, dfa0));

  Dfa dfa5 = dfa0;
  dfa5.ac[2] = 1;
  assert(!isIsomorphic(dfa0, dfa5));
  assert(!isIsomorphic(dfa5, dfa0));
}

void unittest_Nfa() {
  // 0*10*(10*10*)* (odd number of 1's)
  Nfa nfa(6, 0, 2);
  nfa.to[0][0].push_back(0);
  nfa.to[0][1].push_back(1);
  nfa.to[1][0].push_back(1);
  nfa.to[3][1].push_back(4);
  nfa.to[4][0].push_back(4);
  nfa.to[4][1].push_back(5);
  nfa.to[5][0].push_back(5);
  nfa.eps[1].push_back(2);
  nfa.eps[2].push_back(3);
  nfa.eps[5].push_back(2);
  nfa.ac[2] = 1;
  const Dfa minDfa = nfa.toDfa().minimize();
  Dfa dfa1(2, 0, 2);
  dfa1.to = {{0, 1}, {1, 0}};
  dfa1.ac = {0, 1};
  assert(isIsomorphic(dfa1, minDfa));
  dfa1.ac = {1, 0};
  assert(!isIsomorphic(dfa1, minDfa));
}

int main() {
  unittest_Dfa(); cerr << "PASSED unittest_Dfa" << endl;
  unittest_isIsomorphic(); cerr << "PASSED unittest_isIsomorphic" << endl;
  unittest_Nfa(); cerr << "PASSED unittest_Nfa" << endl;
  return 0;
}
