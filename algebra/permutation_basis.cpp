#include <assert.h>
#include <vector>

using std::vector;

// G: permutation group (<= \S_[0,n))
// G[u] := G \cap \S_[u,n),  G = G[0] >= G[1] >= ... >= G[n-1] >= G[n] = 1
// R[u]: transversal of G[u]/G[u+1] containing 1
// g \in G  <->  r[0] r[1] ... r[n-1]  (r[u] \in R[u])
//   on[u][v] <=> \exists g \in R[u] s.t. g(u) = v
//   rCnt[u] = |R[u]|
//   r[u][v] \in R[u],  r[u][v](u) = v
//   s[u][0, sLen[u]) generates G[u]
template <int N> struct PermBasis {
  int n;
  bool on[N][N];
  int rCnt[N];
  int r[N][N][N], invR[N][N][N];
  int sLen[N];
  int s[N][3 * N / 2][N];

  PermBasis() {}
  explicit PermBasis(int n_) : n(n_), on{}, rCnt{}, r{}, invR{}, sLen{}, s{} {
    assert(0 <= n); assert(n <= N);
    for (int u = 0; u < n; ++u) {
      on[u][u] = true;
      rCnt[u] = 1;
      for (int w = u; w < n; ++w) r[u][u][w] = invR[u][u][w] = w;
    }
  }
  bool contains(int u, const int *g) const {
    if (u == n) return true;
    const int v = g[u];
    if (!on[u][v]) return false;
    // contains(u + 1, r[u][v]^-1 g)
    int h[N] = {};
    for (int w = u; w < n; ++w) h[w] = invR[u][v][g[w]];
    return contains(u + 1, h);
  }
  bool contains(const vector<int> &g) const {
    return contains(0, g.data());
  }
  void add(int u, const int *g) {
    if (contains(u, g)) return;
    for (int w = u; w < n; ++w) s[u][sLen[u]][w] = g[w];
    ++sLen[u];
    int h[N] = {};
    for (int v = u; v < n; ++v) if (on[u][v]) {
      // dfs(u, g r[u][v])
      for (int w = u; w < n; ++w) h[w] = g[r[u][v][w]];
      dfs(u, h);
    }
  }
  void add(const vector<int> &g) {
    return add(0, g.data());
  }
  void dfs(int u, const int *g) {
    const int v = g[u];
    int h[N] = {};
    if (on[u][v]) {
      // add(u + 1, r[u][v]^-1 g)
      for (int w = u + 1; w < n; ++w) h[w] = invR[u][v][g[w]];
      add(u + 1, h);
    } else {
      on[u][v] = true;
      ++rCnt[u];
      for (int w = u; w < n; ++w) invR[u][v][r[u][v][w] = g[w]] = w;
      for (int i = 0; i < sLen[u]; ++i) {
        // dfs(u, s[u][i] g)
        for (int w = u; w < n; ++w) h[w] = s[u][i][g[w]];
        dfs(u, h);
      }
    }
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <algorithm>
#include <iostream>
#include <queue>
#include <random>
#include <utility>

using std::cerr;
using std::endl;
using std::mt19937_64;
using std::queue;
using std::swap;

void unittest() {
  for (int n = 0; n <= 7; ++n) {
    vector<vector<int>> sym;
    {
      vector<int> g(n);
      for (int u = 0; u < n; ++u) g[u] = u;
      do {
        sym.push_back(g);
      } while (std::next_permutation(g.begin(), g.end()));
    }
    const int facN = sym.size();
    vector<vector<int>> mul(facN, vector<int>(facN));
    for (int i = 0; i < facN; ++i) for (int j = 0; j < facN; ++j) {
      vector<int> g(n);
      for (int u = 0; u < n; ++u) g[u] = sym[i][sym[j][u]];
      mul[i][j] = std::lower_bound(sym.begin(), sym.end(), g) - sym.begin();
    }
    for (int caseId = 0; caseId < 100; ++caseId) {
      mt19937_64 rng(caseId);
      vector<int> vis(facN, 0);
      vis[0] = 1;
      PermBasis<7> pb(n);
      assert(pb.contains(sym[0]));
      for (int i = 1; i < facN; ++i) assert(!pb.contains(sym[i]));
      vector<int> is(facN);
      for (int i = 0; i < facN; ++i) swap(is[rng() % (i + 1)], is[i] = i);
      for (const int i : is) {
        if (!vis[i]) {
          queue<int> que;
          vis[i] = 1;
          que.push(i);
          for (; que.size(); ) {
            const int j = que.front();
            que.pop();
            for (int k = 0; k < facN; ++k) if (vis[k]) {
              for (const int l : {mul[j][k], mul[k][j]}) if (!vis[l]) {
                vis[l] = 1;
                que.push(l);
              }
            }
          }
        }
        vector<int> expected(n + 1, 0);
        for (int j = 0; j < facN; ++j) if (vis[j]) {
          for (int u = 0; ; ++u) {
            ++expected[u];
            if (u == n || sym[j][u] != u) break;
          }
        }
        pb.add(sym[i]);
        vector<int> actual(n + 1);
        actual[n] = 1;
        for (int u = n; --u >= 0; ) actual[u] = pb.rCnt[u] * actual[u + 1];
        assert(expected == actual);
        for (int j = 0; j < facN; ++j) assert(vis[j] == pb.contains(sym[j]));
      }
    }
    cerr << "[unittest] PASSED n = " << n << endl;
  }
}

// https://codeforces.com/blog/entry/111290
// https://codeforces.com/gym/421334/problem/A
void gym421334() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    PermBasis<50> pb(N);
    for (int q = 0; q < Q; ++q) {
      vector<int> P(N);
      for (int u = 0; u < N; ++u) {
        scanf("%d", &P[u]);
        --P[u];
      }
      pb.add(P);
    }
    // 50! < 10^65
    constexpr int L = 70;
    int ans[L + 1] = {1};
    for (int u = 0; u < N; ++u) {
      for (int i = 0; i < L; ++i) {
        ans[i] *= pb.rCnt[u];
      }
      for (int i = 0; i < L; ++i) {
        ans[i + 1] += ans[i] / 10;
        ans[i] %= 10;
      }
    }
    int i;
    for (i = L; !ans[i]; --i) {}
    for (; i >= 0; --i) putchar('0' + ans[i]);
    puts("");
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // gym421334();
  return 0;
}
