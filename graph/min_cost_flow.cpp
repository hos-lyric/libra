#include <string.h>
#include <algorithm>
using std::min;

using Int = long long;

namespace MCF {

using Capa = int;
using Cost = Int;
constexpr int MAX_N = 2'010;
constexpr int MAX_M = 1'002'010;
constexpr int QUE_SIZE = 1 << (32 - __builtin_clz(MAX_N));
constexpr int BELLMAN_FORD_NUM_ITERS = 10;
constexpr int LOG_SCALING = 2;

int n, m, ptr[MAX_N], cur[MAX_N], next[MAX_M << 1], zu[MAX_M << 1];
bool on[MAX_N];
int que[QUE_SIZE], qb, qe;
Capa capa[MAX_M << 1], ex[MAX_N];
Cost cost[MAX_M << 1], pot[MAX_N], pot0[MAX_N];

void init(int n_) {
  n = n_; m = 0; memset(ptr, ~0, n * sizeof(int)); memset(ex, 0, n * sizeof(Capa));
}
void ae(int u, int v, Capa c, Cost d) {
  d *= (n + 1);
  next[m] = ptr[u]; ptr[u] = m; zu[m] = v; capa[m] = c; cost[m] = d; ++m;
  next[m] = ptr[v]; ptr[v] = m; zu[m] = u; capa[m] = 0; cost[m] = -d; ++m;
}

bool bellmanFord(Cost eps) {
  memcpy(pot0, pot, n * sizeof(Cost));
  for (int iter = 0; iter < BELLMAN_FORD_NUM_ITERS; ++iter) {
    bool upd = false;
    for (int i = 0; i < m; ++i) {
      if (capa[i] > 0) {
        const int u = zu[i ^ 1], v = zu[i];
        if (pot0[v] > pot0[u] + cost[i] + eps) {
          pot0[v] = pot0[u] + cost[i] + eps;
          upd = true;
        }
      }
    }
    if (!upd) {
      memcpy(pot, pot0, n * sizeof(Cost));
      return true;
    }
  }
  return false;
}

Cost solve() {
  Cost minCost = 0;
  for (int i = 0; i < m; i += 2) if (minCost > cost[i]) minCost = cost[i];
  Cost eps = 1;
  for (; eps < -minCost; eps <<= LOG_SCALING) {}
  memset(pot, 0, n * sizeof(Cost));
  for (; eps >>= LOG_SCALING; ) {
    if (bellmanFord(eps)) continue;
    for (int i = 0; i < m; i += 2) {
      const int u = zu[i ^ 1], v = zu[i];
      const Cost d = cost[i] + pot[u] - pot[v];
      if (capa[i] > 0 && d < 0) {
        Capa &c = capa[i]; ex[u] -= c; ex[v] += c; capa[i ^ 1] += c; c = 0;
      } else if (capa[i ^ 1] > 0 && -d < 0) {
        Capa &c = capa[i ^ 1]; ex[v] -= c; ex[u] += c; capa[i] += c; c = 0;
      }
    }
    memcpy(cur, ptr, n * sizeof(int));
    qb = qe = 0;
    for (int u = 0; u < n; ++u) if (ex[u] > 0) {
      que[qe] = u; ++qe &= QUE_SIZE - 1;
    }
    for (; qb != qe; ) {
      const int u = que[qb]; ++qb &= QUE_SIZE - 1;
      for (int &i = cur[u]; ~i; i = next[i]) {
        if (capa[i] > 0) {
          const int v = zu[i];
          if (cost[i] + pot[u] - pot[v] < 0) {
            const Capa c = min(ex[u], capa[i]);
            if (ex[v] <= 0 && ex[v] + c > 0) {
              que[qe] = v; ++qe &= QUE_SIZE - 1;
            }
            ex[u] -= c; ex[v] += c; capa[i] -= c; capa[i ^ 1] += c;
            if (ex[u] == 0) break;
          }
        }
      }
      if (ex[u] > 0) {
        bool relabeled = false;
        for (int i = ptr[u]; ~i; i = next[i]) {
          if (capa[i] > 0) {
            const Cost p = pot[zu[i]] - cost[i] - eps;
            if (!relabeled || pot[u] < p) {
              relabeled = true; pot[u] = p;
            }
          }
        }
        cur[u] = ptr[u]; que[qe] = u; ++qe &= QUE_SIZE - 1;
      }
    }
  }
  Cost totalCost = 0;
  for (int i = 0; i < m; i += 2) totalCost += cost[i] * capa[i ^ 1];
  return totalCost / (n + 1);
}

}  // namespace MCF


// https://atcoder.jp/contests/agc034/tasks/agc034_d
/*
#include <stdio.h>
#include <vector>
using namespace std;
int main() {
  int N;
  for (; ~scanf("%d", &N); ) {
    vector<Int> X(N * 2), Y(N * 2), C(N * 2);
    for (int u = 0; u < N * 2; ++u) {
      scanf("%lld%lld%lld", &X[u], &Y[u], &C[u]);
    }
    
    MCF::init(N * 2 + 1);
    for (int u = 0; u < N; ++u) {
      MCF::ae(N * 2, u, C[u], 0);
    }
    for (int v = N; v < N * 2; ++v) {
      MCF::ae(v, N * 2, C[v], 0);
    }
    for (int u = 0; u < N; ++u) for (int v = N; v < N * 2; ++v) {
      MCF::ae(u, v, min(C[u], C[v]), -(abs(X[u] - X[v]) + abs(Y[u] - Y[v])));
    }
    const Int res = MCF::solve();
    printf("%lld\n", -res);
  }
  return 0;
}
//*/

// https://judge.yosupo.jp/problem/assignment
//*
#include <stdio.h>
#include <algorithm>
#include <vector>
using namespace std;
int main() {
  int N;
  for (; ~scanf("%d", &N); ) {
    vector<vector<Int>> A(N, vector<Int>(N));
    for (int u = 0; u < N; ++u) for (int v = 0; v < N; ++v) {
      scanf("%lld", &A[u][v]);
    }
    MCF::init(N * 2 + 1);
    Int ans = 0;
    vector<vector<int>> ids(N, vector<int>(N));
    for (int u = 0; u < N; ++u) {
      MCF::ae(N * 2, u, 1, 0);
    }
    for (int v = 0; v < N; ++v) {
      MCF::ae(N + v, N * 2, 1, 0);
    }
    for (int u = 0; u < N; ++u) {
      const Int offset = *max_element(A[u].begin(), A[u].end()) + 1;
      ans += offset;
      for (int v = 0; v < N; ++v) {
        ids[u][v] = MCF::m;
        MCF::ae(u, N + v, 1, A[u][v] - offset);
      }
    }
    ans += MCF::solve();
    printf("%lld\n", ans);
    for (int u = 0; u < N; ++u) {
      if (u > 0) printf(" ");
      for (int v = 0; v < N; ++v) {
        if (MCF::capa[ids[u][v] ^ 1] != 0) {
          printf("%d", v);
        }
      }
    }
    puts("");
  }
  return 0;
}
//*/
