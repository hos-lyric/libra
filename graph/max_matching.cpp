// TODO: understand

#include <assert.h>
#include <queue>
#include <utility>
#include <vector>

using std::make_pair;
using std::pair;
using std::swap;
using std::vector;

// sz: size of the matching
// mate[u]: matching mate of u or -1
// need[u]: every max matching contains u? (call run(true))
struct MaxMatch {
  int n, sz;
  vector<vector<int>> graph;
  vector<int> mate, need;
  MaxMatch() {}
  MaxMatch(int n_) : n(n_), graph(n_) {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    if (u != v) {
      graph[u].push_back(v);
      graph[v].push_back(u);
    }
  }

  vector<int> ts, ps;
  vector<pair<int, int>> fs;
  int root(int u) {
    return (ts[u] != sz || !~ps[u]) ? u : (ps[u] = root(ps[u]));
  }
  void rematch(int u, int v) {
    const int w = mate[u];
    mate[u] = v;
    if (~w && mate[w] == u) {
      if (~fs[u].second) {
        rematch(fs[u].first, fs[u].second);
        rematch(fs[u].second, fs[u].first);
      } else {
        mate[w] = fs[u].first;
        rematch(fs[u].first, w);
      }
    }
  }
  int augment(int src) {
    std::queue<int> que;
    ts[src] = sz;
    ps[src] = -1;
    fs[src] = make_pair(-1, -1);
    que.push(src);
    for (; !que.empty();) {
      int u = que.front();
      que.pop();
      for (const int v : graph[u]) if (v != src) {
        if (mate[v] == -1) {
          mate[v] = u;
          rematch(u, v);
          return 1;
        }
        if (ts[v] == sz) {
          int x = root(u), y = root(v), z = src;
          if (x == y) continue;
          for (; x != src || y != src; x = root(fs[mate[x]].first)) {
            if (y != src) swap(x, y);
            if (fs[x].first == u && fs[x].second == v) {
              z = x;
              break;
            }
            fs[x] = make_pair(u, v);
          }
          for (const int r : {root(u), root(v)}) {
            for (int w = r; w != z; w = root(fs[mate[w]].first)) {
              ts[w] = sz;
              ps[w] = z;
              que.push(w);
            }
          }
        } else if (ts[mate[v]] != sz) {
          fs[v] = make_pair(-1, -1);
          ts[mate[v]] = sz;
          ps[mate[v]] = v;
          fs[mate[v]] = make_pair(u, -1);
          que.push(mate[v]);
        }
      }
    }
    return 0;
  }
  void run(bool buildNeed = false) {
    sz = 0;
    mate.assign(n, -1);
    ts.assign(n, -1);
    ps.assign(n, -1);
    fs.assign(n, make_pair(-1, -1));
    for (int u = 0; u < n; ++u) if (!~mate[u]) sz += augment(u);
    if (buildNeed) {
      for (int u = 0; u < n; ++u) if (!~mate[u]) augment(u);
      need.resize(n);
      for (int u = 0; u < n; ++u) need[u] = (~mate[u] && ts[u] != sz) ? 1 : 0;
    }
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <iostream>

using std::cerr;
using std::endl;

void unittest() {
  {
    MaxMatch mxm(6);
    mxm.ae(0, 1);
    mxm.ae(1, 2);
    mxm.ae(1, 2);
    mxm.ae(1, 3);
    mxm.ae(3, 3);
    mxm.ae(3, 4);
    mxm.ae(4, 5);
    mxm.ae(5, 3);
    mxm.run(true);
    assert(mxm.sz == 2);
    assert(mxm.mate == (vector<int>{1, 0, -1, 4, 3, -1}));
    assert(mxm.need == (vector<int>{0, 1, 0, 0, 0, 0}));
  }
  for (int n = 0; n <= 7; ++n) {
    for (int p = 0; p < 1 << (n * (n - 1) / 2); ++p) {
      vector<pair<int, int>> edges;
      {
        int pp = p;
        for (int u = 0; u < n; ++u) for (int v = u + 1; v < n; ++v) {
          if (pp & 1) edges.emplace_back(u, v);
          pp >>= 1;
        }
      }
      vector<int> brt(1 << n, 0);
      for (int q = 0; q < 1 << n; ++q) {
        for (const auto &edge : edges) {
          const int u = edge.first, v = edge.second;
          if ((q & 1 << u) && (q & 1 << v)) {
            const int tmp = 1 + brt[q - (1 << u) - (1 << v)];
            if (brt[q] < tmp) brt[q] = tmp;
          }
        }
      }
      MaxMatch mxm(n);
      for (const auto &edge : edges) mxm.ae(edge.first, edge.second);
      mxm.run(true);
      assert(brt[(1 << n) - 1] == mxm.sz);
      int cnt = 0;
      for (int u = 0; u < n; ++u) {
        const int v = mxm.mate[u];
        if (~v) {
          ++cnt;
          assert(u == mxm.mate[v]);
          bool hasEdge = false;
          for (const auto &edge : edges) {
            hasEdge = hasEdge || (edge == make_pair(u, v));
            hasEdge = hasEdge || (edge == make_pair(v, u));
          }
          assert(hasEdge);
        }
      }
      assert(cnt == 2 * mxm.sz);
      for (int u = 0; u < n; ++u) {
        assert(brt[(1 << n) - 1] - brt[(1 << n) - 1 - (1 << u)] == mxm.need[u]);
      }
    }
    cerr << "DONE n = " << n << endl;
  }
}

// https://judge.yosupo.jp/problem/general_matching
void yosupo__general_matching() {
  int N, M;
  for (; ~scanf("%d%d", &N, &M); ) {
    MaxMatch mxm(N);
    for (int i = 0; i < M; ++i) {
      int u, v;
      scanf("%d%d", &u, &v);
      mxm.ae(u, v);
    }
    mxm.run(false);
    printf("%d\n", mxm.sz);
    for (int u = 0; u < N; ++u) if (u < mxm.mate[u]) {
      printf("%d %d\n", u, mxm.mate[u]);
    }
  }
}

// https://uoj.ac/problem/79
void uoj_79() {
  int N, M;
  for (; ~scanf("%d%d", &N, &M); ) {
    MaxMatch mxm(N);
    for (int i = 0; i < M; ++i) {
      int u, v;
      scanf("%d%d", &u, &v);
      --u;
      --v;
      mxm.ae(u, v);
    }
    mxm.run(false);
    printf("%d\n", mxm.sz);
    for (int u = 0; u < N; ++u) {
      if (u) printf(" ");
      printf("%d", mxm.mate[u] + 1);
    }
    puts("");
  }
}

// https://www.codechef.com/problems/HAMILG
void codechef_HAMILG() {
  for (int numCases; ~scanf("%d", &numCases); ) {
    for (int caseId = 0; caseId < numCases; ++caseId) {
      int N, M;
      scanf("%d%d", &N, &M);
      MaxMatch mxm(N);
      for (int i = 0; i < M; ++i) {
        int u, v;
        scanf("%d%d", &u, &v);
        --u;
        --v;
        mxm.ae(u, v);
      }
      mxm.run(true);
      int ans = 0;
      for (int u = 0; u < N; ++u) if (!mxm.need[u]) ++ans;
      printf("%d\n", ans);
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupo__general_matching();
  // uoj_79();
  // codechef_HAMILG();
  return 0;
}
