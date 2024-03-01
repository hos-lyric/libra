#include <assert.h>
#include <stdio.h>
#include <vector>

using std::vector;

struct Scc {
  int n;
  vector<int> as, bs;
  vector<int> ptr, zu, us;

  int l;
  vector<int> ids;
  int operator[](int u) const { return ids[u]; }

  explicit Scc(int n_) : n(n_), as(), bs(), l(-1) {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    as.push_back(u);
    bs.push_back(v);
  }

  void dfs0(int u) {
    if (!ids[u]) {
      ids[u] = -1;
      for (int i = ptr[u]; i < ptr[u + 1]; ++i) dfs0(zu[i]);
      us.push_back(u);
    }
  }
  void dfs1(int u) {
    if (!~ids[u]) {
      ids[u] = l;
      for (int i = ptr[u]; i < ptr[u + 1]; ++i) dfs1(zu[i]);
    }
  }
  void run() {
    const int m = as.size();
    ptr.resize(n + 2);
    zu.resize(m);
    for (int u = 0; u < n + 2; ++u) ptr[u] = 0;
    for (int i = 0; i < m; ++i) ++ptr[as[i] + 2];
    for (int u = 2; u < n + 1; ++u) ptr[u + 1] += ptr[u];
    for (int i = 0; i < m; ++i) zu[ptr[as[i] + 1]++] = bs[i];
    ids.assign(n, 0);
    us.clear();
    for (int u = 0; u < n; ++u) dfs0(u);
    for (int u = 0; u < n + 2; ++u) ptr[u] = 0;
    for (int i = 0; i < m; ++i) ++ptr[bs[i] + 2];
    for (int u = 2; u < n + 1; ++u) ptr[u + 1] += ptr[u];
    for (int i = 0; i < m; ++i) zu[ptr[bs[i] + 1]++] = as[i];
    l = 0;
    for (int j = n; --j >= 0; ) if (!~ids[us[j]]) { dfs1(us[j]); ++l; }
  }

  vector<vector<int>> group() const {
    assert(~l);
    vector<vector<int>> uss(l);
    for (int u = 0; u < n; ++u) uss[ids[u]].push_back(u);
    return uss;
  }
};  // Scc

// get0(u): should return a neighbor of u and remove it (or -1).
// get1(u): the same for reversed edge
template <class Get0, class Get1> struct SccDyn {
  int n;
  const Get0 get0;
  const Get1 get1;

  int l;
  vector<int> ids;
  int operator[](int u) const { return ids[u]; }

  SccDyn(int n_, Get0 get0_, Get1 get1_) : n(n_), get0(get0_), get1(get1_) {
    ids.assign(n, 0);
    us.clear();
    for (int u = 0; u < n; ++u) dfs0(u);
    l = 0;
    for (int j = n; --j >= 0; ) if (!~ids[us[j]]) { dfs1(us[j]); ++l; }
  }

  vector<int> us;
  void dfs0(int u) {
    if (!ids[u]) {
      ids[u] = -1;
      for (; ; ) {
        const int v = get0(u);
        if (!~v) break;
        dfs0(v);
      }
      us.push_back(u);
    }
  }
  void dfs1(int u) {
    if (!~ids[u]) {
      ids[u] = l;
      for (; ; ) {
        const int v = get1(u);
        if (!~v) break;
        dfs1(v);
      }
    }
  }

  vector<vector<int>> group() const {
    assert(~l);
    vector<vector<int>> uss(l);
    for (int u = 0; u < n; ++u) uss[ids[u]].push_back(u);
    return uss;
  }
};  // SccDyn
template <class Get0, class Get1>
SccDyn<Get0, Get1> sccDyn(int n, Get0 get0, Get1 get1) {
  return SccDyn<Get0, Get1>(n, get0, get1);
}
template <class Get> auto sccDyn(int n, Get get) {
  return sccDyn(
    n,
    [&](int u) -> int { return get(0, u); },
    [&](int u) -> int { return get(1, u); }
  );
}

////////////////////////////////////////////////////////////////////////////////

#include <algorithm>
#include <iostream>

using std::cerr;
using std::endl;

void unittest_Scc() {
  Scc scc(11);
  scc.ae(7, 5);
  scc.ae(0, 5);
  scc.ae(5, 5);
  scc.ae(0, 6);
  scc.ae(6, 2);
  scc.ae(2, 1);
  scc.ae(1, 6);
  scc.ae(8, 1);
  scc.ae(9, 7);
  scc.ae(3, 9);
  scc.ae(3, 10);
  scc.ae(7, 3);
  scc.ae(0, 10);
  scc.ae(10, 0);
  scc.ae(4, 0);
  scc.ae(4, 0);
  scc.ae(8, 1);
  scc.ae(6, 8);
  scc.run();

  assert(scc.l == 5);
  const vector<int> expected{2, 3, 3, 1, 0, 4, 3, 1, 3, 1, 2};
  for (int u = 0; u < 11; ++u) assert(scc[u] == expected[u]);
  const vector<vector<int>> uss = scc.group();
  assert(uss.size() == 5);
  assert(uss[0] == (vector<int>{4}));
  assert(uss[1] == (vector<int>{3, 7, 9}));
  assert(uss[2] == (vector<int>{0, 10}));
  assert(uss[3] == (vector<int>{1, 2, 6, 8}));
  assert(uss[4] == (vector<int>{5}));
}

void unittest_SccDyn() {
  constexpr int n = 11;
  vector<vector<vector<int>>> graphs(2, vector<vector<int>>(n));
  auto ae = [&](int u, int v) -> void {
    graphs[0][u].push_back(v);
    graphs[1][v].push_back(u);
  };
  auto get = [&](int h, int u) -> int {
    if (graphs[h][u].empty()) return -1;
    const int v = graphs[h][u].back();
    graphs[h][u].pop_back();
    return v;
  };
  ae(7, 5);
  ae(0, 5);
  ae(5, 5);
  ae(0, 6);
  ae(6, 2);
  ae(2, 1);
  ae(1, 6);
  ae(8, 1);
  ae(9, 7);
  ae(3, 9);
  ae(3, 10);
  ae(7, 3);
  ae(0, 10);
  ae(10, 0);
  ae(4, 0);
  ae(4, 0);
  ae(8, 1);
  ae(6, 8);
  // to have the same output as scc
  for (int h = 0; h < 2; ++h) for (int u = 0; u < n; ++u) {
    std::reverse(graphs[h][u].begin(), graphs[h][u].end());
  }
  const auto scc = sccDyn(n, get);
  for (int h = 0; h < 2; ++h) for (int u = 0; u < n; ++u) {
    assert(graphs[h][u].empty());
  }

  assert(scc.l == 5);
  const vector<int> expected{2, 3, 3, 1, 0, 4, 3, 1, 3, 1, 2};
  for (int u = 0; u < 11; ++u) assert(scc[u] == expected[u]);
  const vector<vector<int>> uss = scc.group();
  assert(uss.size() == 5);
  assert(uss[0] == (vector<int>{4}));
  assert(uss[1] == (vector<int>{3, 7, 9}));
  assert(uss[2] == (vector<int>{0, 10}));
  assert(uss[3] == (vector<int>{1, 2, 6, 8}));
  assert(uss[4] == (vector<int>{5}));
}

// https://judge.yosupo.jp/problem/scc
#include <stdio.h>
void yosupo__scc() {
  int N, M;
  scanf("%d%d", &N, &M);
  Scc scc(N);
  for (int i = 0; i < M; ++i) {
    int u, v;
    scanf("%d%d", &u, &v);
    scc.ae(u, v);
  }
  scc.run();
  const vector<vector<int>> uss = scc.group();
  printf("%d\n", scc.l);
  for (int x = 0; x < scc.l; ++x) {
    printf("%d", (int)uss[x].size());
    for (const int u : uss[x]) {
      printf(" %d", u);
    }
    puts("");
  }
}
void yosupo__scc__sccDyn() {
  int N, M;
  scanf("%d%d", &N, &M);
  vector<vector<vector<int>>> graphs(2, vector<vector<int>>(N));
  for (int i = 0; i < M; ++i) {
    int u, v;
    scanf("%d%d", &u, &v);
    graphs[0][u].push_back(v);
    graphs[1][v].push_back(u);
  }
  auto get = [&](int h, int u) -> int {
    if (graphs[h][u].empty()) return -1;
    const int v = graphs[h][u].back();
    graphs[h][u].pop_back();
    return v;
  };
  const auto scc = sccDyn(N, get);
  const vector<vector<int>> uss = scc.group();
  printf("%d\n", scc.l);
  for (int x = 0; x < scc.l; ++x) {
    printf("%d", (int)uss[x].size());
    for (const int u : uss[x]) {
      printf(" %d", u);
    }
    puts("");
  }
}

int main() {
  unittest_Scc(); cerr << "PASSED unittest_Scc" << endl;
  unittest_SccDyn(); cerr << "PASSED unittest_SccDyn" << endl;
  // yosupo__scc();
  // yosupo__scc__sccDyn();
  return 0;
}
