#include <iostream>
using namespace std;

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
constexpr int LOG_SCALING = 2;
int n, m, ptr[MAX_N], cur[MAX_N], next[MAX_M << 1], zu[MAX_M << 1];
bool on[MAX_N];
int que[QUE_SIZE], qb, qe, cnt[MAX_N];
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

bool spfa(Cost eps) {
cerr<<"spfa eps = "<<eps<<endl;
  memset(cnt, 0, n * sizeof(int));
  memcpy(pot0, pot, n * sizeof(Cost));
  qb = qe = 0;
  for (int u = 0; u < n; ++u) {
    que[qe] = u; ++qe &= QUE_SIZE - 1;
    on[u] = true;
  }
  for (; qb != qe; ) {
    const int u = que[qb]; ++qb &= QUE_SIZE - 1;
    on[u] = false;
if(cnt[u]>=n-1)cerr<<"  false"<<endl;
    if (++cnt[u] >= n) return false;
    for (int i = ptr[u]; ~i; i = next[i]) {
      if (capa[i] > 0) {
        const int v = zu[i];
        if (pot0[v] > pot0[u] + cost[i] + eps) {
          pot0[v] = pot0[u] + cost[i] + eps;
          if (!on[v]) {
            que[qe] = v; ++qe &= QUE_SIZE - 1;
            on[v] = true;
          }
        }
      }
    }
  }
  memcpy(pot, pot0, n * sizeof(Cost));
cerr<<"  true"<<endl;
  return true;
}

// Int numPushes,numRelabels;
Cost solve() {
  Cost minCost = 0;
  for (int i = 0; i < m; i += 2) if (minCost > cost[i]) minCost = cost[i];
  Cost eps = 1;
  for (; eps < -minCost; eps <<= LOG_SCALING) {}
  memset(pot, 0, n * sizeof(Cost));
// numPushes=numRelabels=0;
  for (; eps >>= LOG_SCALING; ) {
    if (spfa(eps)) continue;
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
// ++numPushes;
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
// ++numRelabels;
        cur[u] = ptr[u]; que[qe] = u; ++qe &= QUE_SIZE - 1;
      }
    }
  }
  Cost totalCost = 0;
  for (int i = 0; i < m; i += 2) totalCost += cost[i] * capa[i ^ 1];
  return totalCost / (n + 1);
}

}  // namespace MCF


#include <stdio.h>
#include <vector>
using namespace std;

// https://atcoder.jp/contests/agc034/tasks/agc034_d
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
// fprintf(stderr,"counters: %lld %lld\n",MCF::numPushes,MCF::numRelabels);
  }
  return 0;
}
