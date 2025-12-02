#include <assert.h>
#include <algorithm>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

using std::make_pair;
using std::ostream;
using std::pair;
using std::string;
using std::swap;
using std::vector;

struct Hld {
  int n, rt;
  // needs to be tree
  // vertex lists
  // modified in build(rt) (parent removed, heavy child first)
  vector<vector<int>> graph;
  vector<int> sz, par, dep;
  int zeit;
  vector<int> dis, fin, sid;
  // head vertex (minimum depth) in heavy path
  vector<int> head;

  Hld() : n(0), rt(-1), zeit(0) {}
  explicit Hld(int n_) : n(n_), rt(-1), graph(n), zeit(0) {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    graph[u].push_back(v);
    graph[v].push_back(u);
  }

  void dfsSz(int u) {
    sz[u] = 1;
    for (const int v : graph[u]) {
      auto it = std::find(graph[v].begin(), graph[v].end(), u);
      if (it != graph[v].end()) graph[v].erase(it);
      par[v] = u;
      dep[v] = dep[u] + 1;
      dfsSz(v);
      sz[u] += sz[v];
    }
  }
  void dfsHld(int u) {
    dis[u] = zeit++;
    const int deg = graph[u].size();
    if (deg > 0) {
      int vm = graph[u][0];
      int jm = 0;
      for (int j = 1; j < deg; ++j) {
        const int v = graph[u][j];
        if (sz[vm] < sz[v]) {
          vm = v;
          jm = j;
        }
      }
      swap(graph[u][0], graph[u][jm]);
      head[vm] = head[u];
      dfsHld(vm);
      for (int j = 1; j < deg; ++j) {
        const int v = graph[u][j];
        head[v] = v;
        dfsHld(v);
      }
    }
    fin[u] = zeit;
  }
  void build(int rt_) {
    assert(0 <= rt_); assert(rt_ < n);
    rt = rt_;
    sz.assign(n, 0);
    par.assign(n, -1);
    dep.assign(n, -1);
    dep[rt] = 0;
    dfsSz(rt);
    zeit = 0;
    dis.assign(n, -1);
    fin.assign(n, -1);
    head.assign(n, -1);
    head[rt] = rt;
    dfsHld(rt);
    assert(zeit == n);
    sid.assign(n, -1);
    for (int u = 0; u < n; ++u) sid[dis[u]] = u;
  }

  friend ostream &operator<<(ostream &os, const Hld &hld) {
    const int maxDep = *max_element(hld.dep.begin(), hld.dep.end());
    vector<string> ss(2 * maxDep + 1);
    int pos = 0, maxPos = 0;
    for (int j = 0; j < hld.n; ++j) {
      const int u = hld.sid[j];
      const int d = hld.dep[u];
      if (hld.head[u] == u) {
        if (j != 0) {
          pos = maxPos + 1;
          ss[2 * d - 1].resize(pos, '-');
          ss[2 * d - 1] += '+';
        }
      } else {
        ss[2 * d - 1].resize(pos, ' ');
        ss[2 * d - 1] += '|';
      }
      ss[2 * d].resize(pos, ' ');
      ss[2 * d] += std::to_string(u);
      if (maxPos < static_cast<int>(ss[2 * d].size())) {
        maxPos = ss[2 * d].size();
      }
    }
    for (int d = 0; d <= 2 * maxDep; ++d) os << ss[d] << '\n';
    return os;
  }

  bool contains(int u, int v) const {
    return (dis[u] <= dis[v] && dis[v] < fin[u]);
  }
  int lca(int u, int v) const {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    for (; head[u] != head[v]; ) (dis[u] > dis[v]) ? (u = par[head[u]]) : (v = par[head[v]]);
    return (dis[u] > dis[v]) ? v : u;
  }
  int jumpUp(int u, int d) const {
    assert(0 <= u); assert(u < n);
    assert(d >= 0);
    if (dep[u] < d) return -1;
    const int tar = dep[u] - d;
    for (u = head[u]; ; u = head[par[u]]) {
      if (dep[u] <= tar) return sid[dis[u] + (tar - dep[u])];
    }
  }
  int jump(int u, int v, int d) const {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    assert(d >= 0);
    const int l = lca(u, v);
    const int du = dep[u] - dep[l], dv = dep[v] - dep[l];
    if (d <= du) {
      return jumpUp(u, d);
    } else if (d <= du + dv) {
      return jumpUp(v, du + dv - d);
    } else {
      return -1;
    }
  }
  // [u, v) or [u, v]
  template <class F> void doPathUp(int u, int v, bool inclusive, F f) const {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    assert(contains(v, u));
    for (; head[u] != head[v]; u = par[head[u]]) f(dis[head[u]], dis[u] + 1);
    if (inclusive) {
      f(dis[v], dis[u] + 1);
    } else {
      if (v != u) f(dis[v] + 1, dis[u] + 1);
    }
  }
  // not path order, include lca(u, v) or not
  template <class F> void doPath(int u, int v, bool inclusive, F f) const {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    const int l = lca(u, v);
    doPathUp(u, l, false, f);
    doPathUp(v, l, inclusive, f);
  }
  // find deepest true for pred: [u, root] -> bool, increasing
  // -1 if !pred(rt)
  template <class Pred> int findUp(int u, Pred pred) const {
    assert(0 <= u); assert(u < n);
    for (; ~u; ) {
      const int h = head[u];
      if (pred(h)) {
        int lo = dis[h], hi = dis[u] + 1;
        for (; lo + 1 < hi; ) {
          const int mid = (lo + hi) / 2;
          (pred(sid[mid]) ? lo : hi) = mid;
        }
        return sid[lo];
      }
      u = par[h];
    }
    return -1;
  }

  // (vs, ps): compressed tree
  // vs: DFS order (sorted by dis)
  // vs[ps[x]]: the parent of vs[x]
  // ids[vs[x]] = x, not set for non-tree vertex
  vector<int> ids;
  pair<vector<int>, vector<int>> compress(vector<int> us) {
    // O(n) first time
    ids.resize(n, -1);
    std::sort(us.begin(), us.end(), [&](int u, int v) -> bool {
      return (dis[u] < dis[v]);
    });
    us.erase(std::unique(us.begin(), us.end()), us.end());
    int usLen = us.size();
    assert(usLen >= 1);
    for (int x = 1; x < usLen; ++x) us.push_back(lca(us[x - 1], us[x]));
    std::sort(us.begin(), us.end(), [&](int u, int v) -> bool {
      return (dis[u] < dis[v]);
    });
    us.erase(std::unique(us.begin(), us.end()), us.end());
    usLen = us.size();
    for (int x = 0; x < usLen; ++x) ids[us[x]] = x;
    vector<int> ps(usLen, -1);
    for (int x = 1; x < usLen; ++x) ps[x] = ids[lca(us[x - 1], us[x])];
    return make_pair(us, ps);
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>

using std::cerr;
using std::endl;
using std::ostringstream;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void unittest() {
  {
    Hld hld(1);
    hld.build(0);
    {
      ostringstream oss;
      oss << hld;
      assert(oss.str() == string(R"(
0
)").substr(1));
    }
    assert(hld.n == 1);
    assert(hld.rt == 0);
    assert(hld.graph == (vector<vector<int>>{{}}));
    assert(hld.sz == (vector<int>{1}));
    assert(hld.par == (vector<int>{-1}));
    assert(hld.dep == (vector<int>{0}));
    assert(hld.dis == (vector<int>{0}));
    assert(hld.fin == (vector<int>{1}));
    assert(hld.head == (vector<int>{0}));
    assert(hld.contains(0, 0));
    assert(hld.lca(0, 0) == 0);
    assert(hld.jumpUp(0, 0) == 0);
    assert(hld.jumpUp(0, 1) == -1);
    assert(hld.jump(0, 0, 0) == 0);
    assert(hld.jump(0, 0, 1) == -1);
    assert(hld.compress({0}) == make_pair(vector<int>{0}, vector<int>{-1}));
    assert(hld.ids == (vector<int>{0}));
  }
  {
    Hld hld(14);
    hld.ae(0, 6);
    hld.ae(0, 9);
    hld.ae(12, 0);
    hld.ae(2, 10);
    hld.ae(1, 2);
    hld.ae(7, 2);
    hld.ae(2, 4);
    hld.ae(2, 13);
    hld.ae(9, 3);
    hld.graph[11].push_back(5);  // to test the modification of graph
    hld.ae(8, 12);
    hld.ae(11, 8);
    hld.ae(7, 8);
    hld.build(8);
    {
      ostringstream oss;
      oss << hld;
      assert(oss.str() == string(R"(
8
|---------+--+
7         11 12
|         |  |
2         5  0
|--+-+-+     |--+
10 1 4 13    9  6
             |
             3
)").substr(1));
    }
    assert(hld.n == 14);
    assert(hld.rt == 8);
    assert(hld.graph == (vector<vector<int>>{
      {9, 6}, {}, {10, 1, 4, 13}, {}, {}, {}, {}, {2}, {7, 11, 12}, {3}, {}, {5}, {0}, {}
    }));
    assert(hld.sz == (vector<int>{4, 1, 5, 1, 1, 1, 1, 6, 14, 2, 1, 2, 5, 1}));
    assert(hld.par == (vector<int>{12, 2, 7, 9, 2, 11, 0, 8, -1, 0, 2, 8, 8, 2}));
    assert(hld.dep == (vector<int>{2, 3, 2, 4, 3, 2, 3, 1, 0, 3, 3, 1, 1, 3}));
    assert(hld.dis == (vector<int>{10, 4, 2, 12, 5, 8, 13, 1, 0, 11, 3, 7, 9, 6}));
    assert(hld.fin == (vector<int>{14, 5, 7, 13, 6, 9, 14, 7, 14, 13, 4, 9, 14, 7}));
    assert(hld.head == (vector<int>{12, 1, 8, 12, 4, 11, 6, 8, 8, 12, 8, 11, 12, 13}));
    assert(hld.contains(8, 8));
    assert(hld.contains(8, 10));
    assert(!hld.contains(10, 8));
    assert(hld.contains(8, 6));
    assert(!hld.contains(6, 8));
    assert(hld.contains(2, 1));
    assert(!hld.contains(1, 2));
    assert(!hld.contains(2, 5));
    assert(hld.lca(8, 8) == 8);
    assert(hld.lca(1, 8) == 8);
    assert(hld.lca(8, 0) == 8);
    assert(hld.lca(1, 0) == 8);
    assert(hld.lca(6, 10) == 8);
    assert(hld.lca(7, 7) == 7);
    assert(hld.lca(7, 2) == 7);
    assert(hld.lca(13, 7) == 7);
    assert(hld.lca(4, 13) == 2);
    assert(hld.lca(6, 9) == 0);
    assert(hld.lca(12, 6) == 12);
    assert(hld.jumpUp(6, 0) == 6);
    assert(hld.jumpUp(6, 1) == 0);
    assert(hld.jumpUp(6, 2) == 12);
    assert(hld.jumpUp(6, 3) == 8);
    assert(hld.jumpUp(6, 4) == -1);
    assert(hld.jumpUp(6, 5) == -1);
    assert(hld.jumpUp(8, 0) == 8);
    assert(hld.jumpUp(8, 1001001001) == -1);
    assert(hld.jumpUp(3, 0) == 3);
    assert(hld.jumpUp(3, 1) == 9);
    assert(hld.jumpUp(3, 2) == 0);
    assert(hld.jumpUp(3, 3) == 12);
    assert(hld.jumpUp(3, 4) == 8);
    assert(hld.jumpUp(3, 5) == -1);
    assert(hld.jump(13, 3, 0) == 13);
    assert(hld.jump(13, 3, 1) == 2);
    assert(hld.jump(13, 3, 2) == 7);
    assert(hld.jump(13, 3, 3) == 8);
    assert(hld.jump(13, 3, 4) == 12);
    assert(hld.jump(13, 3, 5) == 0);
    assert(hld.jump(13, 3, 6) == 9);
    assert(hld.jump(13, 3, 7) == 3);
    assert(hld.jump(13, 3, 8) == -1);
    assert(hld.jump(5, 8, 0) == 5);
    assert(hld.jump(5, 8, 1) == 11);
    assert(hld.jump(5, 8, 2) == 8);
    assert(hld.jump(5, 8, 3) == -1);
    assert(hld.jump(12, 6, 0) == 12);
    assert(hld.jump(12, 6, 1) == 0);
    assert(hld.jump(12, 6, 2) == 6);
    assert(hld.jump(12, 6, 3) == -1);
    {
      vector<int> ls, rs;
      hld.doPathUp(6, 8, /*inclusive=*/false, [&](int l, int r) -> void {
        ls.push_back(l);
        rs.push_back(r);
      });
      assert(ls == (vector<int>{13, 9}));
      assert(rs == (vector<int>{14, 11}));
    }
    {
      vector<int> ls, rs;
      hld.doPathUp(6, 8, /*inclusive=*/true, [&](int l, int r) -> void {
        ls.push_back(l);
        rs.push_back(r);
      });
      assert(ls == (vector<int>{13, 9, 0}));
      assert(rs == (vector<int>{14, 11, 1}));
    }
    {
      vector<int> ls, rs;
      hld.doPath(4, 3, /*inclusive=*/false, [&](int l, int r) -> void {
        ls.push_back(l);
        rs.push_back(r);
      });
      assert(ls == (vector<int>{5, 1, 9}));
      assert(rs == (vector<int>{6, 3, 13}));
    }
    {
      vector<int> ls, rs;
      hld.doPath(4, 3, /*inclusive=*/true, [&](int l, int r) -> void {
        ls.push_back(l);
        rs.push_back(r);
      });
      assert(ls == (vector<int>{5, 1, 9, 0}));
      assert(rs == (vector<int>{6, 3, 13, 1}));
    }
    {
      vector<int> ls, rs;
      hld.doPath(6, 3, /*inclusive=*/false, [&](int l, int r) -> void {
        ls.push_back(l);
        rs.push_back(r);
      });
      assert(ls == (vector<int>{13, 11}));
      assert(rs == (vector<int>{14, 13}));
    }
    {
      vector<int> ls, rs;
      hld.doPath(6, 3, /*inclusive=*/true, [&](int l, int r) -> void {
        ls.push_back(l);
        rs.push_back(r);
      });
      assert(ls == (vector<int>{13, 10}));
      assert(rs == (vector<int>{14, 13}));
    }
    assert(hld.findUp(6, [&](int u) -> bool {
      assert(u == 8 || u == 12 || u == 0 || u == 6);
      return (u == 8 || u == 12);
    }) == 12);
    assert(hld.compress({6, 3}) ==
           make_pair(vector<int>{0, 3, 6}, vector<int>{-1, 0, 0}));
    assert(hld.ids[0] == 0);
    assert(hld.ids[3] == 1);
    assert(hld.ids[6] == 2);
    assert(hld.compress({1, 3, 4, 7, 8}) ==
           make_pair(vector<int>{8, 7, 2, 1, 4, 3}, vector<int>{-1, 0, 1, 2, 2, 0}));
    assert(hld.ids[8] == 0);
    assert(hld.ids[7] == 1);
    assert(hld.ids[2] == 2);
    assert(hld.ids[1] == 3);
    assert(hld.ids[4] == 4);
    assert(hld.ids[3] == 5);
/*
8
|---------+--+
7         11 12
|         |  |
2         5  0
|--+-+-+     |--+
10 1 4 13    9  6
             |
             3
*/
  }
  {
    constexpr int NUM_CASES = 1000;
    constexpr int MAX_N = 50;
    constexpr int NUM_QUERIES_COMPRESS = 100;
    for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
      const int N = 1 + xrand() % MAX_N;
      vector<vector<int>> dist(N, vector<int>(N, N));
      for (int u = 0; u < N; ++u) dist[u][u] = 0;
      Hld hld(N);
      for (int v = 1; v < N; ++v) {
        const int u = xrand() % v;
        dist[u][v] = 1;
        hld.ae(u, v);
      }
      for (int w = 0; w < N; ++w) for (int u = 0; u < N; ++u) for (int v = 0; v < N; ++v) {
        if (dist[u][v] > dist[u][w] + dist[w][v]) {
          dist[u][v] = dist[u][w] + dist[w][v];
        }
      }
      hld.build(0);
      for (int u = 0; u < N; ++u) {
        for (const int v : hld.graph[u]) {
          assert(hld.sz[hld.graph[u][0]] >= hld.sz[v]);
        }
      }
      // contains
      for (int u = 0; u < N; ++u) for (int v = 0; v < N; ++v) {
        assert(hld.contains(u, v) == (dist[u][v] < N));
      }
      // lca
      for (int u = 0; u < N; ++u) for (int v = 0; v < N; ++v) {
        int l = 0;
        for (int w = 0; w < N; ++w) if (dist[w][u] < N && dist[w][v] < N) {
          if (dist[l][w] < N) {
            l = w;
          }
        }
        assert(hld.lca(u, v) == l);
      }
      // jumpUp
      for (int u = 0; u < N; ++u) {
        vector<int> vs(N + 1, -1);
        for (int v = 0; v < N; ++v) if (dist[v][u] < N) {
          assert(!~vs[dist[v][u]]);
          vs[dist[v][u]] = v;
        }
        for (int d = 0; d <= N; ++d) {
          assert(hld.jumpUp(u, d) == vs[d]);
        }
      }
      // doPathUp
      for (int u = 0; u < N; ++u) for (int v = 0; v < N; ++v) if (dist[v][u] < N) {
        vector<int> expected, actual;
        for (int w = 0; w < N; ++w) if (dist[w][u] < N && dist[v][w] < N && w != v) {
          expected.push_back(w);
        }
        std::sort(expected.begin(), expected.end());
        hld.doPathUp(u, v, /*inclusive=*/false, [&](int l, int r) -> void {
          assert(0 <= l); assert(l < r); assert(r <= N);
          for (int j = l; j < r; ++j) actual.push_back(hld.sid[j]);
        });
        std::sort(actual.begin(), actual.end());
        assert(expected == actual);
      }
      for (int u = 0; u < N; ++u) for (int v = 0; v < N; ++v) if (dist[v][u] < N) {
        vector<int> expected, actual;
        for (int w = 0; w < N; ++w) if (dist[w][u] < N && dist[v][w] < N) {
          expected.push_back(w);
        }
        std::sort(expected.begin(), expected.end());
        hld.doPathUp(u, v, /*inclusive=*/true, [&](int l, int r) -> void {
          assert(0 <= l); assert(l < r); assert(r <= N);
          for (int j = l; j < r; ++j) actual.push_back(hld.sid[j]);
        });
        std::sort(actual.begin(), actual.end());
        assert(expected == actual);
      }
      
      // dist: undirected
      for (int u = 0; u < N; ++u) for (int v = 0; v < N; ++v) if (dist[u][v] == 1) {
        dist[v][u] = 1;
      }
      for (int w = 0; w < N; ++w) for (int u = 0; u < N; ++u) for (int v = 0; v < N; ++v) {
        if (dist[u][v] > dist[u][w] + dist[w][v]) {
          dist[u][v] = dist[u][w] + dist[w][v];
        }
      }
      // jump
      for (int u = 0; u < N; ++u) for (int v = 0; v < N; ++v) {
        vector<int> ws(N + 1, -1);
        for (int w = 0; w < N; ++w) if (dist[u][v] == dist[u][w] + dist[w][v]) {
          assert(!~ws[dist[u][w]]);
          ws[dist[u][w]] = w;
        }
        for (int d = 0; d <= N; ++d) {
          assert(hld.jump(u, v, d) == ws[d]);
        }
      }
      // doPath
      for (int u = 0; u < N; ++u) for (int v = 0; v < N; ++v) {
        vector<int> expected, actual;
        for (int w = 0; w < N; ++w) if (dist[u][v] == dist[u][w] + dist[w][v]) {
          expected.push_back(w);
        }
        std::sort(expected.begin(), expected.end());
        // lca(u, v) has minimum id
        expected.erase(expected.begin());
        hld.doPath(u, v, /*inclusive=*/false, [&](int l, int r) -> void {
          assert(0 <= l); assert(l < r); assert(r <= N);
          for (int j = l; j < r; ++j) actual.push_back(hld.sid[j]);
        });
        std::sort(actual.begin(), actual.end());
        assert(expected == actual);
      }
      for (int u = 0; u < N; ++u) for (int v = 0; v < N; ++v) {
        vector<int> expected, actual;
        for (int w = 0; w < N; ++w) if (dist[u][v] == dist[u][w] + dist[w][v]) {
          expected.push_back(w);
        }
        std::sort(expected.begin(), expected.end());
        hld.doPath(u, v, /*inclusive=*/true, [&](int l, int r) -> void {
          assert(0 <= l); assert(l < r); assert(r <= N);
          for (int j = l; j < r; ++j) actual.push_back(hld.sid[j]);
        });
        std::sort(actual.begin(), actual.end());
        assert(expected == actual);
      }
      // findUp
      for (int u = 0; u < N; ++u) {
        vector<int> fs(N, -1);
        auto pred = [&](int v) -> bool {
          assert(~fs[v]);
          return fs[v];
        };
        vector<int> vs;
        for (int v = u; ~v; v = hld.par[v]) vs.push_back(v);
        const int vsLen = vs.size();
        for (int k = 0; k < vsLen; ++k) fs[vs[k]] = 0;
        assert(hld.findUp(u, pred) == -1);
        for (int k = vsLen; --k >= 0; ) {
          fs[vs[k]] = 1;
          assert(hld.findUp(u, pred) == vs[k]);
        }
      }
      // compress
      for (int q = 0; q < NUM_QUERIES_COMPRESS; ++q) {
        vector<int> us(N);
        for (int u = 0; u < N; ++u) {
          swap(us[xrand() % (u + 1)], us[u] = u);
        }
        const int usLen = 1 + xrand() % N;
        us.resize(usLen);
        vector<int> on(N, 0), dp(N, 0), vs;
        for (const int u : us) on[u] = dp[u] = 1;
        for (int j = N; --j >= 0; ) {
          const int u = hld.sid[j];
          if (dp[u] > 1) {
            on[u] = 1;
            dp[u] = 1;
          }
          if (on[u]) {
            vs.push_back(u);
          }
          if (~hld.par[u]) {
            dp[hld.par[u]] += dp[u];
          }
        }
        reverse(vs.begin(), vs.end());
        const int vsLen = vs.size();
        const auto res = hld.compress(us);
        assert(res.first == vs);
        assert(static_cast<int>(res.second.size()) == vsLen);
        assert(res.second[0] == -1);
        for (int x = 1; x < usLen; ++x) {
          assert(0 <= res.second[x]); assert(res.second[x] < x);
          assert(hld.contains(vs[res.second[x]], vs[x]));
        }
      }
    }
  }
}

#include <stdio.h>

// https://judge.yosupo.jp/problem/lca
void yosupo__lca() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    Hld hld(N);
    for (int u = 1; u < N; ++u) {
      int p;
      scanf("%d", &p);
      hld.ae(p, u);
    }
    hld.build(0);
    for (int q = 0; q < Q; ++q) {
      int u, v;
      scanf("%d%d", &u, &v);
      const int l = hld.lca(u, v);
      printf("%d\n", l);
    }
  }
}

// https://judge.yosupo.jp/problem/jump_on_tree
void yosupo__jump_on_tree() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    Hld hld(N);
    for (int i = 0; i < N - 1; ++i) {
      int u, v;
      scanf("%d%d", &u, &v);
      hld.ae(u, v);
    }
    hld.build(0);
    for (int q = 0; q < Q; ++q) {
      int u, v, d;
      scanf("%d%d%d", &u, &v, &d);
      const int w = hld.jump(u, v, d);
      printf("%d\n", w);
    }
  }
}

// https://judge.yosupo.jp/problem/vertex_add_path_sum
void yosupo__vertex_add_path_sum() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    vector<int> C(N);
    for (int u = 0; u < N; ++u) {
      scanf("%d", &C[u]);
    }
    Hld hld(N);
    for (int i = 0; i < N - 1; ++i) {
      int u, v;
      scanf("%d%d", &u, &v);
      hld.ae(u, v);
    }
    hld.build(0);
    vector<long long> bit(N);
    for (int u = 0; u < N; ++u) {
      bit[hld.dis[u]] = C[u];
    }
    for (int x = 0; x < N; ++x) if ((x | (x + 1)) < N) bit[x | (x + 1)] += bit[x];
    for (int q = 0; q < Q; ++q) {
      int typ;
      scanf("%d", &typ);
      switch (typ) {
        case 0: {
          int u;
          int c;
          scanf("%d%d", &u, &c);
          for (int x = hld.dis[u]; x < N; x |= x + 1) bit[x] += c;
        } break;
        case 1: {
          int u, v;
          scanf("%d%d", &u, &v);
          long long ans = 0;
          hld.doPath(u, v, /*inclusive=*/true, [&](int l, int r) -> void {
            for (int x = l; x > 0; x &= x - 1) ans -= bit[x - 1];
            for (int x = r; x > 0; x &= x - 1) ans += bit[x - 1];
          });
          printf("%lld\n", ans);
        } break;
        default: assert(false);
      }
    }
  }
}

// https://judge.yosupo.jp/problem/vertex_add_subtree_sum
void yosupo__vertex_add_subtree_sum() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    vector<int> C(N);
    for (int u = 0; u < N; ++u) {
      scanf("%d", &C[u]);
    }
    Hld hld(N);
    for (int u = 1; u < N; ++u) {
      int p;
      scanf("%d", &p);
      hld.ae(p, u);
    }
    hld.build(0);
    vector<long long> bit(N);
    for (int u = 0; u < N; ++u) {
      bit[hld.dis[u]] = C[u];
    }
    for (int x = 0; x < N; ++x) if ((x | (x + 1)) < N) bit[x | (x + 1)] += bit[x];
    for (int q = 0; q < Q; ++q) {
      int typ;
      scanf("%d", &typ);
      switch (typ) {
        case 0: {
          int u;
          int c;
          scanf("%d%d", &u, &c);
          for (int x = hld.dis[u]; x < N; x |= x + 1) bit[x] += c;
        } break;
        case 1: {
          int u;
          scanf("%d", &u);
          long long ans = 0;
          for (int x = hld.dis[u]; x > 0; x &= x - 1) ans -= bit[x - 1];
          for (int x = hld.fin[u]; x > 0; x &= x - 1) ans += bit[x - 1];
          printf("%lld\n", ans);
        } break;
        default: assert(false);
      }
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupo__lca();
  // yosupo__jump_on_tree();
  // yosupo__vertex_add_path_sum();
  // yosupo__vertex_add_subtree_sum();
  return 0;
}
