#include <assert.h>
#include <map>
#include <queue>
#include <set>
#include <vector>

using std::vector;

struct Dfa {
  int n, s, a;
  vector<vector<int>> to;
  vector<bool> ac;
  Dfa(int n, int s, int a) : n(n), s(s), a(a) {
    to.assign(n, vector<int>(a, -1));
    ac.assign(n, false);
  }
  int addState() {
    const int u = n++;
    to.emplace_back(a, -1);
    ac.push_back(false);
    return u;
  }

  vector<int> ids;
  vector<vector<int>> uss;
  vector<vector<vector<int>>> revs;
  Dfa minimize() {
    for (int u = 0; u < n; ++u) for (int e = 0; e < a; ++e) {
      assert(to[u][e] != -1);
    }
    std::queue<int> que;
    ids.assign(n, -1);
    // BFS to find reachable states
    ids[s] = -2;
    que.push(s);
    for (; !que.empty(); ) {
      const int u = que.front(); que.pop();
      for (int e = 0; e < a; ++e) {
        if (ids[to[u][e]] == -1) {
          ids[to[u][e]] = -2;
          que.push(to[u][e]);
        }
      }
    }
    // partition
    revs.assign(n, vector<vector<int>>(a));
    for (int u = 0; u < n; ++u) {
      if (ids[u] != -1) {
        for (int e = 0; e < a; ++e) revs[to[u][e]][e].push_back(u);
      }
    }
    int nn = 2;
    uss.assign(n, {});
    for (int u = 0; u < n; ++u) {
      if (ids[u] == -2) uss[ids[u] = ac[u] ? 1 : 0].push_back(u);
    }
    // empty, all
    if (uss[1].empty() || uss[0].empty()) {
      Dfa dfa(1, 0, a);
      dfa.to[0].assign(a, 0);
      dfa.ac[0] = uss[0].empty();
      return dfa;
    }
    que.push((uss[1].size() <= uss[0].size()) ? 1 : 0);
    for (; !que.empty(); ) {
      const int x = que.front(); que.pop();
      std::set<int> parter(uss[x].begin(), uss[x].end());
      for (int e = 0; e < a; ++e) {
        std::set<int> apps;
        for (const int u : parter) for (const int v : revs[u][e]) {
          apps.insert(ids[v]);
        }
        for (const int y : apps) {
          vector<int> vs1, vs0;
          for (const int v : uss[y]) {
            (parter.count(to[v][e]) ? vs1 : vs0).push_back(v);
          }
          if (!vs0.empty()) {
            if (vs1.size() < vs0.size()) vs1.swap(vs0);
            for (const int v : vs0) ids[v] = nn;
            que.push(nn);
            uss[y].swap(vs1);
            uss[nn++].swap(vs0);
          }
        }
      }
    }
    uss.resize(nn);
    // make new DFA
    Dfa dfa(nn, ids[s], a);
    for (int x = 0; x < nn; ++x) {
      const int u = uss[x][0];
      for (int e = 0; e < a; ++e) dfa.to[x][e] = ids[to[u][e]];
      dfa.ac[x] = ac[u];
    }
    return dfa;
  }
};

bool isIsomorphic(const Dfa &dfa0, const Dfa &dfa1) {
  if (dfa0.n != dfa1.n) return false;
  if (dfa0.a != dfa1.a) return false;
  const int n = dfa0.n, a = dfa0.a;
  vector<int> f01(n, -1), f10(n, -1);
  std::queue<int> que;
  f10[f01[dfa0.s] = dfa1.s] = dfa0.s;
  que.push(dfa0.s);
  que.push(dfa1.s);
  for (; !que.empty(); ) {
    const int u0 = que.front(); que.pop();
    const int u1 = que.front(); que.pop();
    for (int e = 0; e < a; ++e) {
      const int v0 = dfa0.to[u0][e], v1 = dfa1.to[u1][e];
      if (f01[v0] == -1 && f10[v1] == -1) {
        f10[f01[v0] = v1] = v0;
        que.push(v0);
        que.push(v1);
      } else {
        if (f01[v0] == -1 || f10[v1] == -1) return false;
        if (f10[f01[v0]] != v0 || f01[f10[v1]] != v1) return false;
      }
    }
  }
  for (int u0 = 0; u0 < n; ++u0) {
    if (f01[u0] != -1 && dfa0.ac[u0] != dfa1.ac[f01[u0]]) return false;
  }
  return true;
}

struct Nfa {
  int n, s, a;
  vector<vector<vector<int>>> to;
  vector<vector<int>> eps;
  vector<bool> ac;
  Nfa(int n, int s, int a) : n(n), s(s), a(a) {
    to.assign(n, vector<vector<int>>(a));
    eps.assign(n, {});
    ac.assign(n, false);
  }
  int addState() {
    const int u = n++;
    to.emplace_back(a);
    eps.emplace_back();
    ac.push_back(false);
    return u;
  }
  Dfa toDfa() const {
    std::queue<int> que;
    vector<std::set<int>> epsed(n);
    for (int u = 0; u < n; ++u) {
      epsed[u].insert(u);
      que.push(u);
      for (; !que.empty(); ) {
        const int v = que.front(); que.pop();
        for (const int w : eps[v]) if (epsed[u].insert(w).second) que.push(w);
      }
    }
    vector<std::set<int>> ps;
    std::map<std::set<int>, int> tr;
    que.push(0);
    ps.push_back(epsed[s]);
    tr[epsed[s]] = 0;
    Dfa dfa(1, 0, a);
    for (; !que.empty(); ) {
      const int x = que.front(); que.pop();
      for (int e = 0; e < a; ++e) {
        std::set<int> pp;
        for (const int u : ps[x]) for (const int v : to[u][e]) {
          for (const int w : epsed[v]) pp.insert(w);
        }
        auto it = tr.find(pp);
        if (it == tr.end()) {
          que.push(dfa.n);
          ps.push_back(pp);
          dfa.to[x][e] = tr[pp] = dfa.n;
          dfa.addState();
        } else {
          dfa.to[x][e] = it->second;
        }
      }
    }
    for (int x = 0; x < dfa.n; ++x) for (const int u : ps[x]) {
      if (ac[u]) dfa.ac[x] = true;
    }
    return dfa;
  }
};

// Dfa
void unittest0() {
  // https://www.cs.wcupa.edu/rkline/fcs/dfa-min.html
  Dfa dfa(7, 1, 2);
  dfa.to = {{1, 2}, {2, 4}, {5, 3}, {2, 6}, {1, 5}, {5, 5}, {3, 5}};
  dfa.ac[1] = dfa.ac[3] = true;
  const Dfa minDfa = dfa.minimize();
  assert(dfa.ids[0] == -1);
  assert(dfa.ids[1] == dfa.ids[3]);
  assert(dfa.ids[4] == dfa.ids[6]);
  assert(minDfa.n == 4);
  assert(minDfa.s == dfa.ids[1]);
  assert(minDfa.a == 2);
  assert(minDfa.to[dfa.ids[1]] == (vector<int>{dfa.ids[2], dfa.ids[4]}));
  assert(minDfa.to[dfa.ids[2]] == (vector<int>{dfa.ids[5], dfa.ids[1]}));
  assert(minDfa.to[dfa.ids[4]] == (vector<int>{dfa.ids[1], dfa.ids[5]}));
  assert(minDfa.to[dfa.ids[5]] == (vector<int>{dfa.ids[5], dfa.ids[5]}));
  assert(minDfa.ac[dfa.ids[1]]);
  assert(!minDfa.ac[dfa.ids[2]]);
  assert(!minDfa.ac[dfa.ids[4]]);
  assert(!minDfa.ac[dfa.ids[5]]);
  Dfa dfa1(4, 0, 2);
  dfa1.to = {{1, 2}, {3, 0}, {0, 3}, {3, 3}};
  dfa1.ac[0] = true;
  assert(isIsomorphic(minDfa, dfa1));
}

// Dfa
void unittest1() {
  // empty
  Dfa dfa0(3, 0, 1);
  dfa0.to = {{1}, {2}, {0}};
  dfa0.ac.assign(3, false);
  dfa0 = dfa0.minimize();
  assert(dfa0.n == 1);
  assert(dfa0.to == (vector<vector<int>>{vector<int>{0}}));
  assert(dfa0.ac == (vector<bool>{false}));
  // all
  Dfa dfa1(3, 0, 1);
  dfa1.to = {{2}, {0}, {1}};
  dfa1.ac.assign(3, true);
  dfa1 = dfa1.minimize();
  assert(dfa1.n == 1);
  assert(dfa1.to == (vector<vector<int>>{vector<int>{0}}));
  assert(dfa1.ac == (vector<bool>{true}));
}

// Nfa
void unittest2() {
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
  nfa.ac[2] = true;
  const Dfa minDfa = nfa.toDfa().minimize();
  Dfa dfa1(2, 0, 2);
  dfa1.to = {{0, 1}, {1, 0}};
  dfa1.ac = {false, true};
  assert(isIsomorphic(dfa1, minDfa));
  dfa1.ac = {true, false};
  assert(!isIsomorphic(dfa1, minDfa));
}

int main() {
  unittest0();
  unittest1();
  unittest2();
  return 0;
}
