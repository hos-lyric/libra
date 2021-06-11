#include <assert.h>
#include <string.h>
#include <vector>

#include "../algebra/modint.h"

constexpr unsigned MO = 998244353U;
using Mint = ModInt<MO>;

// G = (V, E): undirected graph
// For A \subseteq E, k(A) := the number of connected components of (V, A)
// T_G(x, y) := \sum_{A\subseteq E} (x - 1)^(k(A) - k(E)) (y - 1)^(k(A) + |A| - |V|)
//   chromatic_G(z) = (-1)^(|V| - k(G)) z^k(G) T_G(1 - z, 0)
//   T_G(0, 2) = the number of strongly connected orientations
//   T_G(1, 1) = the number of spanning forests (i.e. k(G) connected components))
//   T_G(1, 2) = the number of spanning subgraphs (i.e. k(G) connected components))
//   T_G(2, 0) = the number of acyclic orientations
//   T_G(2, 1) = the number of forests
//   T_G(2, 2) = 2^|E|

// tutte::eval assumes that the graph is simple.

////////////////////////////////////////////////////////////////////////////////
namespace tutte {

constexpr int MAX_N = 21;

Mint inv[MAX_N + 1];
struct ModIntPreparator {
  ModIntPreparator() {
    inv[1] = 1;
    for (int i = 2; i <= MAX_N; ++i) inv[i] = -((Mint::M / i) * inv[Mint::M % i]);
  }
} modIntPreparator;

void setExp(int n, Mint *as) {
  static Mint zas[1 << MAX_N][MAX_N + 1];
  assert(!as[0]);
  for (int h = 1; h < 1 << n; ++h) memset(zas[h] + 1, 0, n * sizeof(Mint));
  for (int h = 1; h < 1 << n; ++h) zas[h][__builtin_popcount(h)] = as[h];
  for (int i = 0; i < n; ++i) for (int h = 1; h < 1 << n; ++h) if (!(h & 1 << i)) {
    for (int k = 1; k <= n; ++k) zas[h | 1 << i][k] += zas[h][k];
  }
  Mint tmp[MAX_N + 1];
  tmp[0] = 1;
  for (int h = 1; h < 1 << n; ++h) {
    for (int k = 1; k <= n; ++k) zas[h][k] *= k;
    for (int k = 1; k <= n; ++k) {
      Mint sum = 0;
      for (int l = 1; l <= k; ++l) sum += zas[h][l] * tmp[k - l];
      tmp[k] = inv[k] * sum;
    }
    memcpy(zas[h] + 1, tmp + 1, n * sizeof(Mint));
  }
  for (int i = 0; i < n; ++i) for (int h = 1; h < 1 << n; ++h) if (!(h & 1 << i)) {
    for (int k = 1; k <= n; ++k) zas[h | 1 << i][k] -= zas[h][k];
  }
  as[0] = 1;
  for (int h = 1; h < 1 << n; ++h) as[h] = zas[h][__builtin_popcount(h)];
}

int n;
int adj[MAX_N];
Mint as[1 << MAX_N];
bool vis[MAX_N];

void init(int n_) {
  assert(n_ >= 0);
  n = n_;
  memset(adj, 0, n * sizeof(int));
}

void ae(int u, int v) {
  assert(0 <= u); assert(u < n);
  assert(0 <= v); assert(v < n);
  adj[u] |= 1 << v;
  adj[v] |= 1 << u;
}

void dfs(int u) {
  if (!vis[u]) {
    vis[u] = true;
    for (int v = 0; v < n; ++v) if (adj[u] & 1 << v) dfs(v);
  }
}

Mint eval(Mint x, Mint y) {
  Mint yys[MAX_N + 1];
  yys[0] = 0;
  for (int i = 0; i < n; ++i) yys[i + 1] = yys[i] * y + 1;
  as[0] = 0;
  for (int u = 0; u < n; ++u) {
    Mint *bs = as + (1 << u);
    for (int h = 0; h < 1 << u; ++h) bs[h] = as[h] * yys[__builtin_popcount(h & adj[u])];
    setExp(u, bs);
  }
  int repr = 0;
  for (int u = 0; u < n; ++u) vis[u] = false;
  for (int u = 0; u < n; ++u) if (!vis[u]) {
    dfs(u);
    repr |= 1 << u;
  }
  for (int h = 0; h < 1 << n; ++h) if (!(h & repr)) as[h] *= (x - 1);
  setExp(n, as);
  return as[(1 << n) - 1];
}

}  // namespace tutte
////////////////////////////////////////////////////////////////////////////////

void unittest() {
  {
    using namespace tutte;
    init(4);
    ae(0, 1);
    ae(1, 2);
    ae(2, 3);
    ae(3, 0);
    ae(0, 2);
    for (int x = -3; x <= +3; ++x) for (int y = -3; y <= +3; ++y) {
      const Mint expected = x * x * x + 2 * x * x + y * y + 2 * x * y + x + y;
      const Mint actual = eval(x, y);
      assert(expected == actual);
    }
  }
}

int main() {
  unittest();
  return 0;
}
