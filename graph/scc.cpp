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
};

////////////////////////////////////////////////////////////////////////////////

void unittest() {
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

// https://judge.yosupo.jp/problem/scc
#include <stdio.h>
void yosupo_scc() {
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

int main() {
  unittest();
  // yosupo_scc();
  return 0;
}
