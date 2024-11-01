#include <assert.h>
#include <algorithm>
#include <limits>
#include <vector>

using std::min;
using std::vector;

template <class Flow> struct MaxFlow {
  // Watch out when using types other than int and long long.
  static constexpr Flow FLOW_EPS = 1e-10L;
  static constexpr Flow FLOW_INF = std::numeric_limits<Flow>::max();
  
  int n, m;
  vector<int> ptr, nxt, zu;
  vector<Flow> capa;

  MaxFlow() {}
  explicit MaxFlow(int n_) : n(n_), m(0), ptr(n_, -1) {}
  void ae(int u, int v, Flow w0, Flow w1 = 0) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    assert(0 <= w0);
    assert(0 <= w1);
    nxt.push_back(ptr[u]); zu.push_back(v); capa.push_back(w0); ptr[u] = m++;
    nxt.push_back(ptr[v]); zu.push_back(u); capa.push_back(w1); ptr[v] = m++;
  }

  vector<int> see, lev, que;

  Flow augment(int u, int t, Flow limFlow) {
    if (u == t) return limFlow;
    for (int &i = see[u]; ~i; i = nxt[i]) if (capa[i] > FLOW_EPS) {
      const int v = zu[i];
      if (lev[u] < lev[v]) {
        const Flow f = augment(v, t, min(limFlow, capa[i]));
        if (f > FLOW_EPS) { capa[i] -= f; capa[i ^ 1] += f; return f; }
      }
    }
    return 0;
  }
  bool bfs(int s, int t) {
    for (int u = 0; u < n; ++u) { see[u] = ptr[u]; lev[u] = -1; }
    auto head = que.begin(), tail = que.begin();
    for (lev[*tail++ = s] = 0; head != tail; ) {
      const int u = *head++;
      for (int i = ptr[u]; ~i; i = nxt[i]) if (capa[i] > FLOW_EPS) {
        const int v = zu[i];
        if (!~lev[v]) {
          lev[*tail++ = v] = lev[u] + 1;
          if (v == t) return true;
        }
      }
    }
    return false;
  }
  Flow run(int s, int t, Flow limFlow = FLOW_INF) {
    see.resize(n); lev.resize(n); que.resize(n);
    Flow flow = 0;
    for (; flow + FLOW_EPS < limFlow && bfs(s, t); ) {
      for (Flow f; (f = augment(s, t, limFlow - flow)) > FLOW_EPS; flow += f) {}
    }
    return flow;
  }
};

////////////////////////////////////////////////////////////////////////////////

void unittest() {
  MaxFlow<int> mcf(4);
  mcf.ae(0, 1, 2);
  mcf.ae(2, 1, 3);
  mcf.ae(3, 0, 3);
  mcf.ae(3, 2, 2);
  mcf.ae(0, 2, 5);
  assert(mcf.run(3, 1) == 5);
}

int main() {
  unittest();
  return 0;
}
