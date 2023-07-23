#include <assert.h>
#include <math.h>
#include <algorithm>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

using std::make_pair;
using std::ostream;
using std::pair;
using std::string;
using std::vector;

struct TreeSqrtDecomp {
  // TODO: optimize
  // larger COEF ==> larger h
  static constexpr int COEF = 1;

  int n, rt;
  vector<pair<int, int>> edges;
  vector<pair<int, int>> paths;

  TreeSqrtDecomp(int n_) : n(n_), rt(-1), edges(), paths(), h(-1) {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    edges.emplace_back(u, v);
  }
  void get(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    paths.emplace_back(u, v);
  }

  vector<int> pt;
  vector<int> g;
  // pre-order
  int usLen;
  vector<int> us;
  vector<int> par;
  int zeit;
  vector<int> dep, dis, fin;
  void dfsBuild(int u) {
    assert(!~dis[u]);  // cycle found
    us[usLen++] = u;
    dis[u] = zeit++;
    for (int j = pt[u]; j < pt[u + 1]; ++j) {
      const int v = g[j];
      if (par[u] != v) {
        par[v] = u;
        dep[v] = dep[u] + 1;
        dfsBuild(v);
      }
    }
    fin[u] = zeit;
  }
  void build(int rt_ = 0) {
    assert(static_cast<int>(edges.size()) == n - 1);
    assert(0 <= rt_); assert(rt_ < n);
    rt = rt_;
    pt.assign(n + 2, 0);
    for (int i = 0; i < n - 1; ++i) {
      const int u = edges[i].first, v = edges[i].second;
      ++pt[u + 2];
      ++pt[v + 2];
    }
    for (int u = 2; u <= n; ++u) pt[u + 1] += pt[u];
    g.resize(2 * (n - 1));
    for (int i = 0; i < n - 1; ++i) {
      const int u = edges[i].first, v = edges[i].second;
      g[pt[u + 1]++] = v;
      g[pt[v + 1]++] = u;
    }
    usLen = 0;
    us.assign(n, -1);
    zeit = 0;
    par.assign(n, -1);
    dep.assign(n, 0);
    dis.assign(n, -1);
    fin.assign(n, -1);
    dfsBuild(rt);
    assert(usLen == n);  // not connected
  }

  // Decompose into subtrees of height <= h.
  //   (# of subtrees) <= ceil(n / (h + 1))
  int h;
  vector<int> hei, rs;
  void decompose(int h_) {
    if (!~rt) build();
    h = h_;
    hei.assign(n, 0);
    for (int k = n; --k >= 1; ) {
      const int u = us[k];
      if (hei[u] < h) {
        const int p = par[u];
        if (hei[p] < 1 + hei[u]) hei[p] = 1 + hei[u];
      }
    }
    rs.resize(n);
    for (const int u : us) {
      rs[u] = (u == rt || hei[u] >= h) ? u : rs[par[u]];
    }
  }
  // Decompose with max h s.t.  q h <= COEF (# of subtrees) n
  //   O(n log n) time
  void decomposeOpt(long long q) {
    int hLo = 0, hHi = n;
    for (; hLo + 1 < hHi; ) {
      const int hMid = (hLo + hHi) / 2;
      decompose(hMid);
      int numSubtrees = 0;
      for (int u = 0; u < n; ++u) if (rs[u] == u) ++numSubtrees;
      ((q * h <= COEF * static_cast<long long>(numSubtrees) * n) ? hLo : hHi) = hMid;
    }
    if (h != hLo) decompose(hLo);
  }

  vector<int> has;
  int opsLen;
  vector<int> ops;
  vector<int> skip;
  vector<int> ord;
  void dfsOps(int u, int p) {
    ord[u] = opsLen;
    for (int j = pt[u]; j < pt[u + 1]; ++j) {
      const int v = g[j];
      if (p != v) {
        const int l = opsLen;
        ops[opsLen++] = v;
        dfsOps(v, u);
        ops[opsLen++] = ~v;
        if (has[v]) {
          has[u] = 1;
        } else {
          skip[l] = opsLen;
        }
      }
    }
  }
  // O(q log q + q h + (# of subtrees) n) time, where q = |path|
  //   init(nL, nR, r)  (# of edges to add at each end)
  //   pushFront(i, v), pushBack(i, v), undoFront(i, v), undoBack(i, v)
  //   query(q)
  template <class Init, class PushFront, class PushBack, class UndoFront, class UndoBack, class Query>
  void run(Init init, PushFront pushFront, PushBack pushBack, UndoFront undoFront, UndoBack undoBack, Query query) {
    const int pathsLen = paths.size();
    if (!~h) decomposeOpt(pathsLen);

    vector<int> up(h + 1);
    auto doPathFront = [&](int u, int v) -> void {
      int upLen = 0;
      auto upU = [&]() -> void {
        up[upLen++] = u;
        u = par[u];
      };
      auto upV = [&]() -> void {
        pushFront(par[v]);
        v = par[v];
      };
      for (; dep[u] > dep[v]; upU()) {}
      for (; dep[u] < dep[v]; upV()) {}
      for (; u != v; upU(), upV()) {}
      for (int l = upLen; --l >= 0; ) pushFront(up[l]);
    };
    auto undoPathFront = [&](int u, int v) -> void {
      int upLen = 0;
      auto upU = [&]() -> void {
        undoFront(u);
        u = par[u];
      };
      auto upV = [&]() -> void {
        up[upLen++] = par[v];
        v = par[v];
      };
      for (; dep[u] > dep[v]; upU()) {}
      for (; dep[u] < dep[v]; upV()) {}
      for (; u != v; upU(), upV()) {}
      for (int l = upLen; --l >= 0; ) undoFront(up[l]);
    };

    vector<pair<int, int>> rqs;
    for (int q = 0; q < pathsLen; ++q) {
      const int u = paths[q].first, v = paths[q].second;
      if (rs[u] == rs[v]) {
        // inside a subtree
        init(2 * h, 0, v);
        doPathFront(u, v);
        query(q);
      } else {
        // r := (first root of a subtree on the path)
        int r;
        if (rs[u] != u && dis[rs[u]] < dis[rs[v]] && dis[rs[v]] < fin[rs[u]]) {
          for (r = rs[v]; ; ) {
            const int rr = rs[par[r]];
            if (rs[u] == rr) break;
            r = rr;
          }
        } else {
          r = rs[u];
        }
        rqs.emplace_back(r, q);
      }
    }
    std::sort(rqs.begin(), rqs.end());
    const int rqsLen = rqs.size();
    has.assign(n, false);
    ops.resize(2 * (n - 1));
    ord.resize(n);
    for (int k0 = 0, k1; k0 < rqsLen; k0 = k1) {
      const int r = rqs[k0].first;
      for (k1 = k0; k1 < rqsLen && r == rqs[k1].first; ++k1) {}
      for (int k = k0; k < k1; ++k) has[paths[rqs[k].second].second] = 1;
      opsLen = 0;
      skip.assign(2 * (n - 1), -1);
      dfsOps(r, -1);
      std::sort(rqs.begin() + k0, rqs.begin() + k1, [&](const pair<int, int> &rq0, const pair<int, int> &rq1) -> bool {
        return (ord[paths[rq0.second].second] < ord[paths[rq1.second].second]);
      });
      init(2 * h + 1, n - 1, r);
      {
        int k = k0;
        auto process = [&](int u) -> void {
          for (; k < k1; ++k) {
            const int q = rqs[k].second;
            if (paths[q].second != u) break;
            doPathFront(paths[q].first, r);
            query(q);
            undoPathFront(paths[q].first, r);
          }
        };
        process(r);
        for (int l = 0; k < k1; ) {
          if (~skip[l]) {
            l = skip[l];
          } else {
            const int v = ops[l];
            if (v >= 0) {
              pushBack(v);
              process(v);
            } else {
              undoBack(~v);
            }
            ++l;
          }
        }
      }
      for (int k = k0; k < k1; ++k) has[paths[rqs[k].second].second] = 0;
    }
  }

  void dfsPrint(ostream &os, int u, const string &branch, int type) const {
    if (type != 0) {
      os << branch << ((type == 1) ? "|" : "`") << "---";
    }
    if (~h && rs[u] == u) {
      os << "[" << u << "]";
    } else {
      os << "(" << u << ")";
    }
    // debug here
    os << "\n";
    int j0 = -1;
    for (int j = pt[u]; j < pt[u + 1]; ++j) if (par[u] != g[j]) j0 = j;
    for (int j = pt[u]; j < pt[u + 1]; ++j) if (par[u] != g[j]) {
      dfsPrint(os, g[j],
               branch + ((type == 0) ? "" : (type == 1) ? "|   " : "    "),
               (j == j0) ? 2 : 1);
    }
  }
  friend ostream &operator<<(ostream &os, const TreeSqrtDecomp &t) {
    t.dfsPrint(os, t.rt, "", 0);
    return os;
  }
};

////////////////////////////////////////////////////////////////////////////////

struct TreeSqrtDecompIV {
  // TODO: optimize
  // larger COEF ==> larger h
  static constexpr int COEF = 1;

  int n, rt;
  vector<pair<int, int>> edges;
  vector<pair<int, int>> paths;

  TreeSqrtDecompIV(int n_) : n(n_), rt(-1), edges(), paths(), h(-1) {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    edges.emplace_back(u, v);
  }
  void get(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    paths.emplace_back(u, v);
  }

  vector<int> pt;
  vector<pair<int, int>> g;
  // pre-order
  int usLen;
  vector<int> us;
  vector<pair<int, int>> par;
  int zeit;
  vector<int> dep, dis, fin;
  void dfsBuild(int u) {
    assert(!~dis[u]);  // cycle found
    us[usLen++] = u;
    dis[u] = zeit++;
    for (int j = pt[u]; j < pt[u + 1]; ++j) if (par[u] != g[j]) {
      const int i = g[j].first;
      const int v = g[j].second;
      par[v] = make_pair(i, u);
      dep[v] = dep[u] + 1;
      dfsBuild(v);
    }
    fin[u] = zeit;
  }
  void build(int rt_ = 0) {
    assert(static_cast<int>(edges.size()) == n - 1);
    assert(0 <= rt_); assert(rt_ < n);
    rt = rt_;
    pt.assign(n + 2, 0);
    for (int i = 0; i < n - 1; ++i) {
      const int u = edges[i].first, v = edges[i].second;
      ++pt[u + 2];
      ++pt[v + 2];
    }
    for (int u = 2; u <= n; ++u) pt[u + 1] += pt[u];
    g.resize(2 * (n - 1));
    for (int i = 0; i < n - 1; ++i) {
      const int u = edges[i].first, v = edges[i].second;
      g[pt[u + 1]++] = make_pair(i, v);
      g[pt[v + 1]++] = make_pair(i, u);
    }
    usLen = 0;
    us.assign(n, -1);
    zeit = 0;
    par.assign(n, make_pair(-1, -1));
    dep.assign(n, 0);
    dis.assign(n, -1);
    fin.assign(n, -1);
    dfsBuild(rt);
    assert(usLen == n);  // not connected
  }

  // Decompose into subtrees of height <= h.
  //   (# of subtrees) <= ceil(n / (h + 1))
  int h;
  vector<int> hei, rs;
  void decompose(int h_) {
    if (!~rt) build();
    h = h_;
    hei.assign(n, 0);
    for (int k = n; --k >= 1; ) {
      const int u = us[k];
      if (hei[u] < h) {
        const int p = par[u].second;
        if (hei[p] < 1 + hei[u]) hei[p] = 1 + hei[u];
      }
    }
    rs.resize(n);
    for (const int u : us) {
      rs[u] = (u == rt || hei[u] >= h) ? u : rs[par[u].second];
    }
  }
  // Decompose with max h s.t.  q h <= COEF (# of subtrees) n
  //   O(n log n) time
  void decomposeOpt(long long q) {
    int hLo = 0, hHi = n;
    for (; hLo + 1 < hHi; ) {
      const int hMid = (hLo + hHi) / 2;
      decompose(hMid);
      int numSubtrees = 0;
      for (int u = 0; u < n; ++u) if (rs[u] == u) ++numSubtrees;
      ((q * h <= COEF * static_cast<long long>(numSubtrees) * n) ? hLo : hHi) = hMid;
    }
    if (h != hLo) decompose(hLo);
  }

  vector<int> has;
  int opsLen;
  vector<pair<int, int>> ops;
  vector<int> skip;
  vector<int> ord;
  void dfsOps(int u, int pi) {
    ord[u] = opsLen;
    for (int j = pt[u]; j < pt[u + 1]; ++j) {
      const int i = g[j].first;
      const int v = g[j].second;
      if (pi != i) {
        const int l = opsLen;
        ops[opsLen++] = make_pair(i, v);
        dfsOps(v, i);
        ops[opsLen++] = make_pair(~i, v);
        if (has[v]) {
          has[u] = 1;
        } else {
          skip[l] = opsLen;
        }
      }
    }
  }
  // O(q log q + q h + (# of subtrees) n) time, where q = |path|
  //   init(nL, nR, r)  (# of edges to add at each end)
  //   pushFront(i, v), pushBack(i, v), undoFront(i, v), undoBack(i, v)
  //   query(q)
  template <class Init, class PushFront, class PushBack, class UndoFront, class UndoBack, class Query>
  void run(Init init, PushFront pushFront, PushBack pushBack, UndoFront undoFront, UndoBack undoBack, Query query) {
    const int pathsLen = paths.size();
    if (!~h) decomposeOpt(pathsLen);

    vector<pair<int, int>> up(h + 1);
    auto doPathFront = [&](int u, int v) -> void {
      int upLen = 0;
      auto upU = [&]() -> void {
        up[upLen++] = make_pair(par[u].first, u);
        u = par[u].second;
      };
      auto upV = [&]() -> void {
        pushFront(par[v].first, par[v].second);
        v = par[v].second;
      };
      for (; dep[u] > dep[v]; upU()) {}
      for (; dep[u] < dep[v]; upV()) {}
      for (; u != v; upU(), upV()) {}
      for (int l = upLen; --l >= 0; ) pushFront(up[l].first, up[l].second);
    };
    auto undoPathFront = [&](int u, int v) -> void {
      int upLen = 0;
      auto upU = [&]() -> void {
        undoFront(par[u].first, u);
        u = par[u].second;
      };
      auto upV = [&]() -> void {
        up[upLen++] = make_pair(par[v].first, par[v].second);
        v = par[v].second;
      };
      for (; dep[u] > dep[v]; upU()) {}
      for (; dep[u] < dep[v]; upV()) {}
      for (; u != v; upU(), upV()) {}
      for (int l = upLen; --l >= 0; ) undoFront(up[l].first, up[l].second);
    };

    vector<pair<int, int>> rqs;
    for (int q = 0; q < pathsLen; ++q) {
      const int u = paths[q].first, v = paths[q].second;
      if (rs[u] == rs[v]) {
        // inside a subtree
        init(2 * h, 0, v);
        doPathFront(u, v);
        query(q);
      } else {
        // r := (first root of a subtree on the path)
        int r;
        if (rs[u] != u && dis[rs[u]] < dis[rs[v]] && dis[rs[v]] < fin[rs[u]]) {
          for (r = rs[v]; ; ) {
            const int rr = rs[par[r].second];
            if (rs[u] == rr) break;
            r = rr;
          }
        } else {
          r = rs[u];
        }
        rqs.emplace_back(r, q);
      }
    }
    std::sort(rqs.begin(), rqs.end());
    const int rqsLen = rqs.size();
    has.assign(n, false);
    ops.resize(2 * (n - 1));
    ord.resize(n);
    for (int k0 = 0, k1; k0 < rqsLen; k0 = k1) {
      const int r = rqs[k0].first;
      for (k1 = k0; k1 < rqsLen && r == rqs[k1].first; ++k1) {}
      for (int k = k0; k < k1; ++k) has[paths[rqs[k].second].second] = 1;
      opsLen = 0;
      skip.assign(2 * (n - 1), -1);
      dfsOps(r, -1);
      std::sort(rqs.begin() + k0, rqs.begin() + k1, [&](const pair<int, int> &rq0, const pair<int, int> &rq1) -> bool {
        return (ord[paths[rq0.second].second] < ord[paths[rq1.second].second]);
      });
      init(2 * h + 1, n - 1, r);
      {
        int k = k0;
        auto process = [&](int u) -> void {
          for (; k < k1; ++k) {
            const int q = rqs[k].second;
            if (paths[q].second != u) break;
            doPathFront(paths[q].first, r);
            query(q);
            undoPathFront(paths[q].first, r);
          }
        };
        process(r);
        for (int l = 0; k < k1; ) {
          if (~skip[l]) {
            l = skip[l];
          } else {
            const int i = ops[l].first;
            const int v = ops[l].second;
            if (i >= 0) {
              pushBack(i, v);
              process(v);
            } else {
              undoBack(~i, v);
            }
            ++l;
          }
        }
      }
      for (int k = k0; k < k1; ++k) has[paths[rqs[k].second].second] = 0;
    }
  }

  void dfsPrint(ostream &os, int u, const string &branch, int type) const {
    if (type != 0) {
      os << branch << ((type == 1) ? "|" : "`") << "---" << par[u].first << "---";
    }
    if (~h && rs[u] == u) {
      os << "[" << u << "]";
    } else {
      os << "(" << u << ")";
    }
    // debug here
    os << "\n";
    int j0 = -1;
    for (int j = pt[u]; j < pt[u + 1]; ++j) if (par[u] != g[j]) j0 = j;
    for (int j = pt[u]; j < pt[u + 1]; ++j) if (par[u] != g[j]) {
      dfsPrint(os, g[j].second,
               branch + ((type == 0) ? "" : (type == 1) ? "|       " : "        "),
               (j == j0) ? 2 : 1);
    }
  }
  friend ostream &operator<<(ostream &os, const TreeSqrtDecompIV &t) {
    t.dfsPrint(os, t.rt, "", 0);
    return os;
  }
};

////////////////////////////////////////////////////////////////////////////////

// TreeSqrtDecomp
/*
    auto init = [&](int nL, int nR, int r) -> void {
cerr<<"init "<<nL<<" "<<nR<<" "<<r<<endl;
      
    };
    auto pushFront = [&](int v) -> void {
cerr<<"pushFront "<<v<<endl;
      
    };
    auto pushBack = [&](int v) -> void {
cerr<<"pushBack "<<v<<endl;
      
    };
    auto undoFront = [&](int v) -> void {
cerr<<"undoFront "<<v<<endl;
      
    };
    auto undoBack = [&](int v) -> void {
cerr<<"undoBack "<<v<<endl;
      
    };
    auto query = [&](int q) -> void {
cerr<<"query "<<q<<endl;
      
    };
    t.run(init, pushFront, pushBack, undoFront, undoBack, query);
*/

// TreeSqrtDecompIV
/*
    auto init = [&](int nL, int nR, int r) -> void {
cerr<<"init "<<nL<<" "<<nR<<" "<<r<<endl;
      
    };
    auto pushFront = [&](int i, int v) -> void {
cerr<<"pushFront "<<i<<" "<<v<<endl;
      
    };
    auto pushBack = [&](int i, int v) -> void {
cerr<<"pushBack "<<i<<" "<<v<<endl;
      
    };
    auto undoFront = [&](int i, int v) -> void {
cerr<<"undoFront "<<i<<" "<<v<<endl;
      
    };
    auto undoBack = [&](int i, int v) -> void {
cerr<<"undoBack "<<i<<" "<<v<<endl;
      
    };
    auto query = [&](int q) -> void {
cerr<<"query "<<q<<endl;
      
    };
    t.run(init, pushFront, pushBack, undoFront, undoBack, query);
*/

#include <iostream>
#include <sstream>

using std::cerr;
using std::endl;
using std::ostringstream;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void unittest_TreeSqrtDecomp() {
  {
    TreeSqrtDecomp t(12);
    vector<vector<int>> dist(t.n, vector<int>(t.n, t.n));
    for (int u = 0; u < t.n; ++u) dist[u][u] = 0;
    auto ae = [&](int u, int v) -> void {
      dist[u][v] = dist[v][u] = 1;
      t.ae(u, v);
    };
    ae(1, 5);
    ae(1, 10);
    ae(1, 9);
    ae(2, 7);
    ae(2, 11);
    ae(2, 4);
    ae(11, 8);
    ae(0, 5);
    ae(7, 9);
    ae(6, 9);
    ae(6, 3);
    for (int w = 0; w < t.n; ++w) for (int u = 0; u < t.n; ++u) for (int v = 0; v < t.n; ++v) {
      if (dist[u][v] > dist[u][w] + dist[w][v]) {
        dist[u][v] = dist[u][w] + dist[w][v];
      }
    }
    t.build(7);
    {
      ostringstream oss;
      oss << t;
      assert(oss.str() == string(R"(
(7)
|---(2)
|   |---(11)
|   |   `---(8)
|   `---(4)
`---(9)
    |---(1)
    |   |---(5)
    |   |   `---(0)
    |   `---(10)
    `---(6)
        `---(3)
)").substr(1));
    }
    t.decompose(1);
    {
      ostringstream oss;
      oss << t;
      assert(oss.str() == string(R"(
[7]
|---[2]
|   |---[11]
|   |   `---(8)
|   `---(4)
`---(9)
    |---[1]
    |   |---[5]
    |   |   `---(0)
    |   `---(10)
    `---[6]
        `---(3)
)").substr(1));
    }
    assert(t.rs == (vector<int>{5, 1, 2, 6, 2, 5, 6, 7, 11, 7, 1, 11}));

    // (h, (# of subtrees)) = (0, 12), (1, 6), (2, 4), (3, 2), (>= 4, 1)
    static_assert(TreeSqrtDecompIV::COEF == 1, "Unittests assume that COEF = 1.");
    t.decomposeOpt(0); assert(t.h == 11);
    t.decomposeOpt(1); assert(t.h == 11);
    t.decomposeOpt(2); assert(t.h == 6);
    t.decomposeOpt(3); assert(t.h == 4);
    t.decomposeOpt(4); assert(t.h == 3);
    t.decomposeOpt(8); assert(t.h == 3);
    t.decomposeOpt(9); assert(t.h == 2);
    t.decomposeOpt(24); assert(t.h == 2);
    t.decomposeOpt(25); assert(t.h == 1);
    t.decomposeOpt(72); assert(t.h == 1);
    t.decomposeOpt(73); assert(t.h == 0);
    t.decomposeOpt(1'000'000'000LL); assert(t.h == 0);

    t.decompose(2);
    {
      ostringstream oss;
      oss << t;
      assert(oss.str() == string(R"(
[7]
|---[2]
|   |---(11)
|   |   `---(8)
|   `---(4)
`---[9]
    |---[1]
    |   |---(5)
    |   |   `---(0)
    |   `---(10)
    `---(6)
        `---(3)
)").substr(1));
    }
    assert(t.rs == (vector<int>{1, 1, 2, 9, 2, 1, 9, 7, 2, 9, 1, 2}));

    for (int u = 0; u < t.n; ++u) for (int v = 0; v < t.n; ++v) {
      t.get(u, v);
    }
    int l = -1, m = -1, r = -1;
    vector<int> xs;
    vector<int> cnt(t.paths.size(), 0);
    auto init = [&](int nL, int nR, int u) -> void {
      xs.assign(nL + 1 + nR, -1);
      xs[l = m = r = nL] = u;
    };
    auto pushFront = [&](int v) -> void {
      assert(l - 1 >= 0); xs[--l] = v;
    };
    auto pushBack = [&](int v) -> void {
      assert(r + 1 < static_cast<int>(xs.size())); xs[++r] = v;
    };
    auto undoFront = [&](int v) -> void {
      assert(l < m); assert(xs[l] == v); ++l;
    };
    auto undoBack = [&](int v) -> void {
      assert(r > m); assert(xs[r] == v); --r;
    };
    auto query = [&](int q) -> void {
      ++cnt[q];
      assert(xs[l] == t.paths[q].first);
      assert(xs[r] == t.paths[q].second);
      assert(dist[xs[l]][xs[r]] == r - l);
      for (int j = l; j <= r; ++j) {
        assert(0 <= xs[j]); assert(xs[j] < t.n);
      }
      for (int j = l; j < r; ++j) {
        assert(dist[xs[j]][xs[j + 1]] == 1);
      }
    };
    t.run(init, pushFront, pushBack, undoFront, undoBack, query);
    assert(cnt == vector<int>(t.paths.size(), 1));
  }
  {
    constexpr int NUM_CASES = 1000;
    constexpr int MAX_N = 200;
    constexpr int MAX_Q = 200;
    for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
      const int N = 1 + xrand() % MAX_N;
      const int Q = 1 + xrand() % MAX_Q;
      vector<vector<int>> dist(N, vector<int>(N, N));
      for (int u = 0; u < N; ++u) dist[u][u] = 0;
      TreeSqrtDecomp t(N);
      for (int v = 1; v < N; ++v) {
        const int u = xrand() % v;
        dist[u][v] = dist[v][u] = 1;
        t.ae(u, v);
      }
      for (int q = 0; q < Q; ++q) {
        const int u = xrand() % N;
        const int v = xrand() % N;
        t.get(u, v);
      }
      for (int w = 0; w < N; ++w) for (int u = 0; u < N; ++u) for (int v = 0; v < N; ++v) {
        if (dist[u][v] > dist[u][w] + dist[w][v]) {
          dist[u][v] = dist[u][w] + dist[w][v];
        }
      }
      int l = -1, m = -1, r = -1;
      vector<int> xs;
      vector<int> cnt(Q, 0);
      auto init = [&](int nL, int nR, int u) -> void {
        xs.assign(nL + 1 + nR, -1);
        xs[l = m = r = nL] = u;
      };
      auto pushFront = [&](int v) -> void {
        assert(l - 1 >= 0); xs[--l] = v;
      };
      auto pushBack = [&](int v) -> void {
        assert(r + 1 < static_cast<int>(xs.size())); xs[++r] = v;
      };
      auto undoFront = [&](int v) -> void {
        assert(l < m); assert(xs[l] == v); ++l;
      };
      auto undoBack = [&](int v) -> void {
        assert(r > m); assert(xs[r] == v); --r;
      };
      auto query = [&](int q) -> void {
        ++cnt[q];
        assert(xs[l] == t.paths[q].first);
        assert(xs[r] == t.paths[q].second);
        assert(dist[xs[l]][xs[r]] == r - l);
        for (int j = l; j <= r; ++j) {
          assert(0 <= xs[j]); assert(xs[j] < t.n);
        }
        for (int j = l; j < r; ++j) {
          assert(dist[xs[j]][xs[j + 1]] == 1);
        }
      };
      t.run(init, pushFront, pushBack, undoFront, undoBack, query);
      assert(cnt == vector<int>(Q, 1));
      // cerr << "N = " << N << ", Q = " << Q << ", h = " << t.h << endl;
    }
  }
}

void unittest_TreeSqrtDecompIV() {
  {
    TreeSqrtDecompIV t(12);
    t.ae(1, 5);
    t.ae(1, 10);
    t.ae(1, 9);
    t.ae(2, 7);
    t.ae(2, 11);
    t.ae(2, 4);
    t.ae(11, 8);
    t.ae(0, 5);
    t.ae(7, 9);
    t.ae(6, 9);
    t.ae(6, 3);
    t.build(7);
    {
      ostringstream oss;
      oss << t;
      assert(oss.str() == string(R"(
(7)
|---3---(2)
|       |---4---(11)
|       |       `---6---(8)
|       `---5---(4)
`---8---(9)
        |---2---(1)
        |       |---0---(5)
        |       |       `---7---(0)
        |       `---1---(10)
        `---9---(6)
                `---10---(3)
)").substr(1));
    }
    t.decompose(1);
    {
      ostringstream oss;
      oss << t;
      assert(oss.str() == string(R"(
[7]
|---3---[2]
|       |---4---[11]
|       |       `---6---(8)
|       `---5---(4)
`---8---(9)
        |---2---[1]
        |       |---0---[5]
        |       |       `---7---(0)
        |       `---1---(10)
        `---9---[6]
                `---10---(3)
)").substr(1));
    }
    assert(t.rs == (vector<int>{5, 1, 2, 6, 2, 5, 6, 7, 11, 7, 1, 11}));

    // (h, (# of subtrees)) = (0, 12), (1, 6), (2, 4), (3, 2), (>= 4, 1)
    static_assert(TreeSqrtDecompIV::COEF == 1, "Unittests assume that COEF = 1.");
    t.decomposeOpt(0); assert(t.h == 11);
    t.decomposeOpt(1); assert(t.h == 11);
    t.decomposeOpt(2); assert(t.h == 6);
    t.decomposeOpt(3); assert(t.h == 4);
    t.decomposeOpt(4); assert(t.h == 3);
    t.decomposeOpt(8); assert(t.h == 3);
    t.decomposeOpt(9); assert(t.h == 2);
    t.decomposeOpt(24); assert(t.h == 2);
    t.decomposeOpt(25); assert(t.h == 1);
    t.decomposeOpt(72); assert(t.h == 1);
    t.decomposeOpt(73); assert(t.h == 0);
    t.decomposeOpt(1'000'000'000LL); assert(t.h == 0);

    t.decompose(2);
    {
      ostringstream oss;
      oss << t;
      assert(oss.str() == string(R"(
[7]
|---3---[2]
|       |---4---(11)
|       |       `---6---(8)
|       `---5---(4)
`---8---[9]
        |---2---[1]
        |       |---0---(5)
        |       |       `---7---(0)
        |       `---1---(10)
        `---9---(6)
                `---10---(3)
)").substr(1));
    }
    assert(t.rs == (vector<int>{1, 1, 2, 9, 2, 1, 9, 7, 2, 9, 1, 2}));

    for (int u = 0; u < t.n; ++u) for (int v = 0; v < t.n; ++v) {
      t.get(u, v);
    }
    int l = -1, m = -1, r = -1;
    vector<int> xs;
    vector<int> cnt(t.paths.size(), 0);
    auto init = [&](int nL, int nR, int u) -> void {
      xs.assign(2 * nL + 1 + 2 * nR, -1);
      xs[l = m = r = 2 * nL] = u;
    };
    auto pushFront = [&](int i, int v) -> void {
      assert(l - 1 >= 0); xs[--l] = i;
      assert(l - 1 >= 0); xs[--l] = v;
    };
    auto pushBack = [&](int i, int v) -> void {
      assert(r + 1 < static_cast<int>(xs.size())); xs[++r] = i;
      assert(r + 1 < static_cast<int>(xs.size())); xs[++r] = v;
    };
    auto undoFront = [&](int i, int v) -> void {
      assert(l < m); assert(xs[l] == v); ++l;
      assert(l < m); assert(xs[l] == i); ++l;
    };
    auto undoBack = [&](int i, int v) -> void {
      assert(r > m); assert(xs[r] == v); --r;
      assert(r > m); assert(xs[r] == i); --r;
    };
    auto query = [&](int q) -> void {
      ++cnt[q];
      assert(xs[l] == t.paths[q].first);
      assert(xs[r] == t.paths[q].second);
      for (int j = l + 1; j <= r - 1; j += 2) {
        const int i = xs[j];
        const int u = xs[j - 1], v = xs[j + 1];
        assert(0 <= i); assert(i < t.n - 1);
        assert(make_pair(u, v) == t.edges[i] || make_pair(v, u) == t.edges[i]);
      }
    };
    t.run(init, pushFront, pushBack, undoFront, undoBack, query);
    assert(cnt == vector<int>(t.paths.size(), 1));
  }
  {
    constexpr int NUM_CASES = 1000;
    constexpr int MAX_N = 200;
    constexpr int MAX_Q = 200;
    for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
      const int N = 1 + xrand() % MAX_N;
      const int Q = 1 + xrand() % MAX_Q;
      TreeSqrtDecompIV t(N);
      for (int v = 1; v < N; ++v) {
        const int u = xrand() % v;
        t.ae(u, v);
      }
      for (int q = 0; q < Q; ++q) {
        const int u = xrand() % N;
        const int v = xrand() % N;
        t.get(u, v);
      }
      int l = -1, m = -1, r = -1;
      vector<int> xs;
      vector<int> cnt(Q, 0);
      auto init = [&](int nL, int nR, int u) -> void {
        xs.assign(2 * nL + 1 + 2 * nR, -1);
        xs[l = m = r = 2 * nL] = u;
      };
      auto pushFront = [&](int i, int v) -> void {
        assert(l - 1 >= 0); xs[--l] = i;
        assert(l - 1 >= 0); xs[--l] = v;
      };
      auto pushBack = [&](int i, int v) -> void {
        assert(r + 1 < static_cast<int>(xs.size())); xs[++r] = i;
        assert(r + 1 < static_cast<int>(xs.size())); xs[++r] = v;
      };
      auto undoFront = [&](int i, int v) -> void {
        assert(l < m); assert(xs[l] == v); ++l;
        assert(l < m); assert(xs[l] == i); ++l;
      };
      auto undoBack = [&](int i, int v) -> void {
        assert(r > m); assert(xs[r] == v); --r;
        assert(r > m); assert(xs[r] == i); --r;
      };
      auto query = [&](int q) -> void {
        ++cnt[q];
        assert(xs[l] == t.paths[q].first);
        assert(xs[r] == t.paths[q].second);
        for (int j = l + 1; j <= r - 1; j += 2) {
          const int i = xs[j];
          const int u = xs[j - 1], v = xs[j + 1];
          assert(0 <= i); assert(i < t.n - 1);
          assert(make_pair(u, v) == t.edges[i] || make_pair(v, u) == t.edges[i]);
        }
      };
      t.run(init, pushFront, pushBack, undoFront, undoBack, query);
      assert(cnt == vector<int>(Q, 1));
      // cerr << "N = " << N << ", Q = " << Q << ", h = " << t.h << endl;
    }
  }
}

int main() {
  unittest_TreeSqrtDecomp(); cerr << "PASSED unittest_TreeSqrtDecomp" << endl;
  unittest_TreeSqrtDecompIV(); cerr << "PASSED unittest_TreeSqrtDecompIV" << endl;
  return 0;
}
