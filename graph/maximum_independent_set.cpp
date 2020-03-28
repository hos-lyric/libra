#include <cassert>
#include <cstdint>
#include <cstring>
#include <algorithm>

int popcnt(__uint128_t x) {
  return __builtin_popcountll(static_cast<uint64_t>(x)) +
         __builtin_popcountll(static_cast<uint64_t>(x >> 64));
}

struct MaxIndSet {
  static constexpr int MAX_N = 128;
  int n;
  __uint128_t adj[MAX_N];
  int optLen;
  int opt[MAX_N], us[MAX_N];
  int psLens[MAX_N];
  int pss[MAX_N + 1][MAX_N];
  __uint128_t groups[MAX_N];
  MaxIndSet(int n) : n(n), adj(), optLen(0), psLens() { assert(n <= MAX_N); }
  void addEdge(int u, int v) {
    adj[u] |= static_cast<__uint128_t>(1) << v;
    adj[v] |= static_cast<__uint128_t>(1) << u;
  }
  void dfs(int len) {
    if (psLens[len] == 0) {
      if (optLen < len) {
        optLen = len;
        std::memcpy(opt, us, sizeof(us[0]) * len);
      }
      return;
    }
    std::sort(pss[len], pss[len] + psLens[len]);
    std::memset(groups, 0, sizeof(groups[0]) * psLens[len]);
    for (int i = psLens[len] - 1; i >= 0; --i) {
      const int u = pss[len][i] & 0xff;
      for (int color = 0; ; ++color) {
        if (!(groups[color] & ~adj[u])) {
          groups[color] |= static_cast<__uint128_t>(1) << u;
          pss[len][i] |= color << 16;
          break;
        }
      }
    }
    std::sort(pss[len], pss[len] + psLens[len]);
    for (int i = psLens[len] - 1; i >= 0; --i) {
      if (optLen >= len + 1 + (pss[len][i] >> 16)) break;
      const int u = pss[len][i] & 0xff;
      __uint128_t sub = 0;
      psLens[len + 1] = 0;
      for (int j = 0; j < i; ++j) {
        const int v = pss[len][j] & 0xff;
        if (!(adj[u] & static_cast<__uint128_t>(1) << v)) {
          sub |= static_cast<__uint128_t>(1) << v;
          pss[len + 1][psLens[len + 1]++] = v;
        }
      }
      for (int j = 0; j < psLens[len + 1]; ++j) {
        const int v = pss[len + 1][j];
        pss[len + 1][j] |= (n - popcnt(adj[v] & sub)) << 8;
      }
      us[len] = u;
      dfs(len + 1);
    }
  }
  int run() {
    std::memset(psLens, 0, sizeof(psLens[0]) * (n + 1));
    for (int u = 0; u < n; ++u) {
      pss[0][psLens[0]++] = (n - popcnt(adj[u])) << 8 | u;
    }
    optLen = 0;
    dfs(0);
    std::sort(opt, opt + optLen);
    return optLen;
  }
};

// https://judge.yosupo.jp/problem/maximum_independent_set
#include <cstdio>
#include <vector>
using namespace std;
int main() {
  int N, M;
  for (; ~scanf("%d%d", &N, &M); ) {
    vector<int> U(M), V(M);
    for (int i = 0; i < M; ++i) {
      scanf("%d%d", &U[i], &V[i]);
    }
    MaxIndSet mis(N);
    for (int i = 0; i < M; ++i) {
      mis.addEdge(U[i], V[i]);
    }
    const int res = mis.run();
    printf("%d\n", res);
    for (int j = 0; j < res; ++j) {
      if (j > 0) printf(" ");
      printf("%d", mis.opt[j]);
    }
    puts("");
  }
  return 0;
}
