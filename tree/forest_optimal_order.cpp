#include <assert.h>
#include <queue>
#include <utility>
#include <vector>

using std::pair;
using std::vector;

// par: must represent a forest.
//   The roots should point to -1 or n.
// T: monoid
//   T()  should return the identity.
//   T::append(const T &t)  should multiply t from right.
//   T::operator<(const T &t)  should represent the order to optimize.
//     Small to large.
//     It must be a weak order (for the possible products of ts).
template <class T>
struct ForestOptimalOrder {
  int n;
  bool isForest;
  T total;
  vector<int> us;
  ForestOptimalOrder() : n(0), isForest(false), total() {}
  ForestOptimalOrder(const vector<int> &par, vector<T> ts)
      : n(par.size()), isForest(false), total() {
    assert(n == static_cast<int>(ts.size()));
    uf.assign(n + 1, -1);
    std::priority_queue<Entry> que;
    vector<int> tails(n + 1, n), nxt(n + 1, -1);
    for (int u = 0; u < n; ++u) que.push(Entry{ts[u], u, tails[u] = u});
    for (; !que.empty(); ) {
      const int v = que.top().head, tail = que.top().tail;
      que.pop();
      if (tails[v] == tail) {
        // v as early as possible ==> right after its parent
        const int u = root((~par[v]) ? par[v] : n);
        if (!connect(u, v)) return;
        nxt[tails[u]] = v; tails[u] = tail;
        if (u == n) {
          total.append(ts[v]);
        } else {
          ts[u].append(ts[v]);
          que.push(Entry{ts[u], u, tails[u]});
        }
      }
    }
    isForest = true;
    us.resize(n);
    for (int j = 0, u = n; j < n; ++j) us[j] = u = nxt[u];
  }

  struct Entry {
    T t;
    int head, tail;
    // reversed order
    bool operator<(const Entry &e) const { return (e.t < t); }
  };

  vector<int> uf;
  int root(int u) {
    return (uf[u] < 0) ? u : (uf[u] = root(uf[u]));
  }
  // root(u) becomes the parent
  bool connect(int u, int v) {
    u = root(u);
    v = root(v);
    if (u == v) return false;
    uf[u] += uf[v];
    uf[v] = u;
    return true;
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>

// https://loj.ac/p/2509
namespace libre2509 {
using Int = long long;
struct Info {
  // (weight, score) -> (weight + a, score + b * weight + c)
  Int a, b, c;
  Info() : a(0), b(0), c(0) {}
  void append(const Info &t) {
    b += t.b;
    c += t.b * a + t.c;
    a += t.a;
  }
  bool operator<(const Info &t) const {
    return (t.b * a > b * t.a);
  }
};
void solve() {
  int N;
  for (; ~scanf("%d", &N); ) {
    vector<int> A(N);
    for (int u = 0; u < N; ++u) {
      scanf("%d", &A[u]);
      --A[u];
    }
    vector<Int> W(N);
    for (int u = 0; u < N; ++u) {
      scanf("%lld", &W[u]);
    }

    vector<Info> ts(N);
    for (int u = 0; u < N; ++u) {
      ts[u].a = 1;
      ts[u].b = W[u];
      ts[u].c = 0;
    }
    const ForestOptimalOrder<Info> foo(A, ts);
    if (foo.isForest) {
      const Int ans = foo.total.b * 1 + foo.total.c;
      printf("%lld\n", ans);
    } else {
      puts("-1");
    }
  }
}
}  // namespace libre2509

int main() {
  // TODO: unittest
  libre2509::solve();
  return 0;
}
