#include <assert.h>
#include <vector>

using std::vector;

// ~ 1.381^n  (n -> n-1, n-4)
// Overflows for empty graph with n = 64.
struct CountIndSet {
  using u64 = unsigned long long;
  int n;
  vector<u64> adj;
  CountIndSet(int n_) : n(n_), adj(n, 0) {
    assert(0 <= n); assert(n <= 64);
  }
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    assert(u != v);
    adj[u] |= 1ULL << v;
    adj[v] |= 1ULL << u;
  }
  u64 run() {
    if (n == 0) return 1;
    path.assign(n + 1, 0);
    cycle.assign(n + 1, 0);
    path[0] = 1; path[1] = 2;
    for (int i = 2; i <= n; ++i) path[i] = path[i - 1] + path[i - 2];
    cycle[0] = 2; cycle[1] = 1;
    for (int i = 2; i <= n; ++i) cycle[i] = cycle[i - 1] + cycle[i - 2];
    return rec((n == 64) ? ~0ULL : ((1ULL << n) - 1));
  }
  vector<u64> path, cycle;
  u64 rec(u64 p) const {
    u64 ans = 1;
    for (; p; ) {
      const int u = __builtin_ctzll(p);
      u64 q = 1ULL << u, r = 0;
      for (; q & ~r; ) {
        const int v = __builtin_ctzll(q & ~r);
        q |= adj[v] & p;
        r |= 1ULL << v;
      }
      ans *= recConnected(q);
      p &= ~q;
    }
    return ans;
  }
  u64 recConnected(u64 p) const {
    if (!p) return 1;
    if (!(p & (p - 1))) return 2;
    int maxDeg = -1, um = -1, cnt1 = 0, cnt2 = 0;
    for (u64 pp = p; pp; ) {
      const int u = __builtin_ctzll(pp);
      pp &= ~(1ULL << u);
      const int deg = __builtin_popcountll(adj[u] & p);
      if (maxDeg < deg) {
        maxDeg = deg;
        um = u;
      }
      if (deg == 1) ++cnt1;
      if (deg == 2) ++cnt2;
    }
    if (maxDeg <= 2) {
      return cnt1 ? path[cnt1 + cnt2] : cycle[cnt2];
    } else {
      p &= ~(1ULL << um);
      return rec(p) + rec(p & ~adj[um]);
    }
  }
};

// ~ 1.381^(sqrt(2m))
// graph needs to be simple.
struct CountClique {
  int n;
  vector<vector<int>> graph;
  CountClique(int n_) : n(n_), graph(n) {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    assert(u != v);
    graph[u].push_back(v);
    graph[v].push_back(u);
  }
  template <class T> T run() const {
    // empty
    T ans = 1;
    vector<int> deg(n), ids(n, -1);
    for (int u = 0; u < n; ++u) deg[u] = graph[u].size();
    for (; ; ) {
      int um = -1;
      for (int u = 0; u < n; ++u) if (~deg[u]) if (!~um || deg[um] > deg[u]) um = u;
      if (!~um) break;
      deg[um] = -1;
      for (const int v : graph[um]) if (~deg[v]) --deg[v];
      // use um (min deg)
      int nn = 0;
      for (const int v : graph[um]) if (~deg[v]) ids[v] = nn++;
      CountIndSet cis(nn);
      for (int x = 0; x < nn; ++x) cis.adj[x] = (nn == 64) ? ~0ULL : ((1ULL << nn) - 1);
      for (const int v : graph[um]) if (~deg[v]) {
        const int x = ids[v];
        cis.adj[x] &= ~(1ULL << x);
        for (const int w : graph[v]) if (~ids[w]) {
          const int y = ids[w];
          cis.adj[x] &= ~(1ULL << y);
          cis.adj[y] &= ~(1ULL << x);
        }
      }
      ans += cis.run();
      for (const int v : graph[um]) if (~deg[v]) ids[v] = -1;
    }
    return ans;
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <string.h>
#include <iostream>

using std::cerr;
using std::endl;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void unittest_CountIndSet() {
  {
    CountIndSet cis(64);
    // 2^64
    assert(cis.run() == 0);
    // path[i] = Fibonacci[i+2]
    assert(cis.path[0] == 1);
    assert(cis.path[1] == 2);
    assert(cis.path[2] == 3);
    assert(cis.path[3] == 5);
    assert(cis.path[64] == 27777890035288ULL);
    // cycle[i] = LucasL[i]  (i <= 2: not used)
    assert(cis.cycle[0] == 2);
    assert(cis.cycle[1] == 1);
    assert(cis.cycle[2] == 3);
    assert(cis.cycle[3] == 4);
    assert(cis.cycle[4] == 7);
    assert(cis.cycle[5] == 11);
    assert(cis.cycle[64] == 23725150497407ULL);
    // K_64
    for (int u = 0; u < 64; ++u) for (int v = 0; v < 64; ++v) if (u != v) {
      cis.ae(u, v);
    }
    assert(cis.run() == 65);
  }
  {
    int n;
    bool adj[64][64];
    auto brute = [&]() -> unsigned long long {
      unsigned long long ans = 0;
      for (int q = 0; q < 1 << n; ++q) {
        bool isInd = true;
        for (int u = 0; u < n; ++u) if (q >> u & 1) {
          for (int v = u + 1; v < n; ++v) if (q >> v & 1) {
            isInd = isInd && !adj[u][v];
          }
        }
        if (isInd) ++ans;
      }
      return ans;
    };
    for (n = 0; n <= 6; ++n) {
      for (int p = 0; p < 1 << (n * (n + 1) / 2); ++p) {
        memset(adj, 0, sizeof(adj));
        CountIndSet cis(n);
        {
          int pp = p;
          for (int u = 0; u < n; ++u) for (int v = u + 1; v < n; ++v) {
            if (pp & 1) {
              adj[u][v] = adj[v][u] = true;
              cis.ae(u, v);
            }
            pp >>= 1;
          }
        }
        const unsigned long long expected = brute();
        const unsigned long long actual = cis.run();
        assert(expected == actual);
      }
    }
    for (n = 7; n <= 20; ++n) {
      memset(adj, 0, sizeof(adj));
      CountIndSet cis(n);
      for (int u = 0; u < n; ++u) for (int v = u + 1; v < n; ++v) {
        if (xrand() & 1) {
          adj[u][v] = adj[v][u] = true;
          cis.ae(u, v);
        }
      }
      const unsigned long long expected = brute();
      const unsigned long long actual = cis.run();
      assert(expected == actual);
    }
  }
}

void unittest_CountClique() {
  {
    CountClique ccl(64);
    assert(ccl.run<int>() == 65);
    for (int u = 0; u < 64; ++u) for (int v = u + 1; v < 64; ++v) {
      ccl.ae(u, v);
    }
    // 2^64
    assert(ccl.run<unsigned long long>() == 0);
  }
  {
    int n;
    bool adj[64][64];
    auto brute = [&]() -> unsigned long long {
      unsigned long long ans = 0;
      for (int q = 0; q < 1 << n; ++q) {
        bool isClique = true;
        for (int u = 0; u < n; ++u) if (q >> u & 1) {
          for (int v = u + 1; v < n; ++v) if (q >> v & 1) {
            isClique = isClique && adj[u][v];
          }
        }
        if (isClique) ++ans;
      }
      return ans;
    };
    for (n = 0; n <= 6; ++n) {
      for (int p = 0; p < 1 << (n * (n + 1) / 2); ++p) {
        memset(adj, 0, sizeof(adj));
        CountClique ccl(n);
        {
          int pp = p;
          for (int u = 0; u < n; ++u) for (int v = u + 1; v < n; ++v) {
            if (pp & 1) {
              adj[u][v] = adj[v][u] = true;
              ccl.ae(u, v);
            }
            pp >>= 1;
          }
        }
        const unsigned long long expected = brute();
        const unsigned long long actual = ccl.run<unsigned long long>();
        assert(expected == actual);
      }
    }
    for (n = 7; n <= 20; ++n) {
      memset(adj, 0, sizeof(adj));
      CountClique ccl(n);
      for (int u = 0; u < n; ++u) for (int v = u + 1; v < n; ++v) {
        if (xrand() & 1) {
          adj[u][v] = adj[v][u] = true;
          ccl.ae(u, v);
        }
      }
      const unsigned long long expected = brute();
      const unsigned long long actual = ccl.run<unsigned long long>();
      assert(expected == actual);
    }
  }
}

// https://qoj.ac/contest/1358/problem/7514
void ucup_2_3_Binjiang_C() {
  constexpr unsigned MO = 1'000'000'007;
  int N, M;
  for (; ~scanf("%d%d", &N, &M); ) {
    CountClique ccl(N);
    for (int i = 0; i < M; ++i) {
      int u, v;
      scanf("%d%d", &u, &v);
      --u;
      --v;
      ccl.ae(u, v);
    }
    const unsigned long long ans = ccl.run<unsigned long long>();
    printf("%llu\n", (ans - 1) % MO);
  }
}

int main() {
  // unittest_CountIndSet(); cerr << "PASSED unittest_CountIndSet" << endl;
  // unittest_CountClique(); cerr << "PASSED unittest_CountClique" << endl;
  ucup_2_3_Binjiang_C();
  return 0;
}
