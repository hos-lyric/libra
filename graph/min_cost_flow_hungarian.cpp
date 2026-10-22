#include <assert.h>
#include <math.h>
#include <utility>
#include <vector>

using std::swap;
using std::vector;

// minimize  \sum[0<=u<m] a[u][ps[u]]  s.t.  ps: [m] -> [n]: injective,  qs = ps^-1
// potential:  a[u][v] >= bs[u] + cs[v],  equality if v = ps[u]
//   cs[v] <= 0,  equality if v is unmatched
// Cost: signed interger,  (2n + 2) (max |a[u][v]|)  should not overflow.
template <class Cost> struct Assignment {
  int m, n;
  Cost total;
  vector<int> ps, qs;
  vector<Cost> bs, cs;

  Assignment() {}
  Assignment(const vector<vector<Cost>> &a) {
    m = a.size();
    if (m == 0) { n = 0; total = 0; ps = qs = {}; bs = cs = {}; return; }
    n = a[0].size();
    for (int u = 0; u < m; ++u) assert(static_cast<int>(a[u].size()) == n);
    assert(m <= n);
    Cost maxA = 0;
    for (int u = 0; u < m; ++u) for (int v = 0; v < n; ++v) if (maxA < abs(a[u][v])) maxA = abs(a[u][v]);
    const Cost inf = 2 * maxA + 1;
    ps.assign(m, -1);
    qs.assign(n, -1);
    // permute columns (use sv = vs^-1 only when augmenting)
    vector<int> vs(n), sv(n);
    for (int v = 0; v < n; ++v) vs[v] = v;
    // pot[j] = cs[vs[j]],  initially bs[u] = \min[v] a[u][v],  cs[v] = 0
    vector<Cost> pot(n, 0);
    // shortest path to vs[j]  (edge cost:  a[u][v] - bs[u] - cs[v])
    vector<Cost> dist(n);
    vector<int> par(n);
    for (int s = 0; s < m; ++s) {
      // vs[0, s): matched, vs[s, n): unmatched
      for (int j = 0; j < n; ++j) dist[j] = inf;
      // (distance to u) - bs[u]  (compute by bs[u] = a[u][ps[u]] - cs[ps[u]])
      Cost c = inf;
      for (int v = 0; v < n; ++v) if (c > a[s][v]) c = a[s][v];
      c = 0 - c;
      int u = s;
      // vs[0, j0): dist determined
      for (int j0 = 0; ; ++j0) {
        Cost minD = dist[j0];
        int j1 = j0;
        for (int j = n; --j >= j0; ) {
          const Cost cc = c + a[u][vs[j]] - pot[j];
          if (dist[j] > cc) {
            dist[j] = cc;
            par[j] = u;
          }
          if (minD > dist[j]) {
            minD = dist[j];
            j1 = j;
          }
        }
        int v = vs[j1];
        if (~qs[v]) {
          swap(vs[j0], vs[j1]);
          swap(pot[j0], pot[j1]);
          swap(dist[j0], dist[j1]);
          swap(par[j0], par[j1]);
          u = qs[v];
          c = minD - (a[u][v] - pot[j0]);
        } else {
          // augment
          for (int j = 0; j < j0; ++j) {
            pot[j] += (dist[j] - minD);
            sv[vs[j]] = j;
          }
          for (int j = j1; ; ) {
            u = par[j];
            const int vv = ps[u];
            ps[u] = v;
            qs[v] = u;
            if (!~vv) break;
            j = sv[vv];
            v = vv;
          }
          swap(vs[s], vs[j1]);
          swap(pot[s], pot[j1]);
          break;
        }
      }
    }
    total = 0;
    for (int u = 0; u < m; ++u) total += a[u][ps[u]];
    bs.resize(m);
    cs.resize(n);
    for (int j = 0; j < n; ++j) cs[vs[j]] = pot[j];
    for (int u = 0; u < m; ++u) bs[u] = a[u][ps[u]] - cs[ps[u]];
  }
};  // Assignment

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <algorithm>
#include <iostream>
#include <random>

using std::cerr;
using std::endl;
using std::mt19937_64;

void unittest() {
  {
    const vector<vector<int>> a{
      {5, 3, 1},
      {4, 9, 1},
    };
    Assignment<int> f(a);
    assert(f.total == 4);
    assert(f.ps == (vector<int>{1, 2}));
    assert(f.qs == (vector<int>{-1, 0, 1}));
  }
  {
    constexpr long long LIM_COST = 1'000'000'000'000'000LL;
    constexpr int NUM_CASES = 1'000;
    mt19937_64 rng;
    for (int m = 0; m <= 8; ++m) for (int n = m; n <= 8; ++n) {
      if (m == 0 && n != 0) continue;
      for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
        vector<vector<long long>> a(m, vector<long long>(n));
        for (int u = 0; u < m; ++u) for (int v = 0; v < n; ++v) {
          a[u][v] = -LIM_COST + rng() % (2 * LIM_COST + 1);
        }
        long long expected = n * LIM_COST + 1;
        {
          vector<int> ps(n);
          for (int v = 0; v < n; ++v) ps[v] = v;
          do {
            long long cost = 0;
            for (int u = 0; u < m; ++u) cost += a[u][ps[u]];
            if (expected > cost) expected = cost;
            std::reverse(ps.begin() + m, ps.end());
          } while (std::next_permutation(ps.begin(), ps.end()));
        }
        const Assignment<long long> f(a);
        assert(expected == f.total);
        assert(m == f.m);
        assert(n == f.n);
        assert(m == static_cast<int>(f.ps.size()));
        assert(n == static_cast<int>(f.qs.size()));
        assert(m == static_cast<int>(f.bs.size()));
        assert(n == static_cast<int>(f.cs.size()));
        long long actual = 0;
        for (int u = 0; u < m; ++u) {
          const int v = f.ps[u];
          assert(0 <= v); assert(v < n);
          assert(u == f.qs[v]);
          actual += a[u][v];
        }
        for (int v = 0; v < n; ++v) {
          const int u = f.qs[v];
          if (~u) assert(f.ps[u] == v);
        }
        assert(f.total == actual);
        for (int u = 0; u < m; ++u) for (int v = 0; v < n; ++v) {
          assert(a[u][v] >= f.bs[u] + f.cs[v]);
          if (f.ps[u] == v) assert(a[u][v] == f.bs[u] + f.cs[v]);
        }
        for (int v = 0; v < n; ++v) {
          assert(f.cs[v] <= 0);
          if (!~f.qs[v]) assert(f.cs[v] == 0);
        }
      }
      cerr << "[unittest] PASSED m = " << m << ", n = " << n << endl;
    }
  }
}

// https://judge.yosupo.jp/problem/assignment
void yosupo_assignment() {
  int N;
  for (; ~scanf("%d", &N); ) {
    vector<vector<long long>> A(N, vector<long long>(N));
    for (int u = 0; u < N; ++u) for (int v = 0; v < N; ++v) scanf("%lld", &A[u][v]);
    const Assignment<long long> f(A);
    printf("%lld\n", f.total);
    for (int u = 0; u < N; ++u) {
      if (u) printf(" ");
      printf("%d", f.ps[u]);
    }
    puts("");
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupo_assignment();
  return 0;
}
