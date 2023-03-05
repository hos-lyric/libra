#include <assert.h>
#include <algorithm>
#include <utility>
#include <vector>

using std::swap;
using std::vector;

// directed, cannot distinguish the outgoing edges
struct Bisimulation {
  int n;
  vector<vector<int>> graph, hparg;

  int nn;
  vector<int> ids;
  vector<vector<int>> uss;

  explicit Bisimulation(int n_) : n(n_), graph(n_), hparg(n_), nn(-1) {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    graph[u].push_back(v);
    hparg[v].push_back(u);
  }
  void run() {
    // separate by degree
    int maxDeg = 0;
    for (int u = 0; u < n; ++u) if (maxDeg < static_cast<int>(graph[u].size())) maxDeg = graph[u].size();
    uss.assign(maxDeg + 1, {});
    for (int u = 0; u < n; ++u) uss[graph[u].size()].push_back(u);
    std::sort(uss.begin(), uss.end(), [&](const vector<int> &us0, const vector<int> &us1) -> bool {
      return (us0.size() > us1.size());
    });
    nn = 0;
    for (int d = 0; d <= maxDeg; ++d) if (!uss[d].empty()) ++nn;
    ids.resize(n);
    vector<int> poss(n);
    for (int x = 0; x < nn; ++x) {
      int pos = 0;
      for (const int u : uss[x]) {
        ids[u] = x;
        poss[u] = pos++;
      }
    }
    // uss as queue
    uss.resize(n, {});
    // vertex to move (reused)
    vector<int> deg(n, 0);
    vector<vector<int>> wss(n);
    for (int x = 1; x < nn; ++x) {
      // partition by degree to uss[x]
      vector<int> ys;
      for (const int u : uss[x]) for (const int v : hparg[u]) {
        const int y = ids[v];
        if (wss[y].empty()) ys.push_back(y);
        if (deg[v]++ == 0) wss[y].push_back(v);
      }
      for (const int y : ys) {
        maxDeg = 0;
        for (const int v : wss[y]) if (maxDeg < deg[v]) maxDeg = deg[v];
        vector<vector<int>> vss(maxDeg + 1);
        uss[y].swap(vss[0]);
        for (const int v : wss[y]) {
          // move v from vss[0] to vss[deg[v]]
          swap(vss[0][poss[v]], vss[0].back());
          poss[vss[0][poss[v]]] = poss[v];
          vss[0].pop_back();
          poss[v] = vss[deg[v]].size();
          vss[deg[v]].push_back(v);
        }
        int dm = 0;
        for (int d = 1; d <= maxDeg; ++d) if (vss[dm].size() < vss[d].size()) dm = d;
        if (dm != 0) for (const int v : vss[dm]) ids[v] = y;
        uss[y].swap(vss[dm]);
        for (int d = 0; d <= maxDeg; ++d) if (!vss[d].empty() && dm != d) {
          const int z = nn++;
          uss[z].swap(vss[d]);
          for (const int v : uss[z]) ids[v] = z;
        }
      }
      for (const int y : ys) {
        for (const int v : wss[y]) deg[v] = 0;
        wss[y].clear();
      }
    }
    uss.resize(nn);
    // to make the output unique
    std::sort(uss.begin(), uss.end());
    for (int x = 0; x < nn; ++x) {
      std::sort(uss[x].begin(), uss[x].end());
      for (const int u : uss[x]) ids[u] = x;
    }
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>

using std::cerr;
using std::endl;

void unittest() {
  {
    Bisimulation b(10);
    b.ae(0, 1);
    b.ae(0, 1);
    b.ae(1, 2);
    b.ae(2, 3);
    b.ae(2, 3);
    b.ae(3, 0);
    b.ae(4, 5);
    b.ae(4, 5);
    b.ae(5, 6);
    b.ae(6, 7);
    b.ae(6, 7);
    b.ae(7, 8);
    b.ae(8, 9);
    b.ae(8, 9);
    b.ae(9, 4);
    b.run();
    assert(b.nn == 2);
    assert(b.ids == (vector<int>{0, 1, 0, 1, 0, 1, 0, 1, 0, 1}));
    assert(b.uss == (vector<vector<int>>{{0, 2, 4, 6, 8}, {1, 3, 5, 7, 9}}));
  }
  {
    Bisimulation b(8);
    b.ae(0, 1);
    b.ae(1, 2);
    b.ae(2, 3);
    b.ae(3, 4);
    b.ae(4, 5);
    b.ae(5, 6);
    b.ae(6, 7);
    b.run();
    assert(b.nn == 8);
    assert(b.ids == (vector<int>{0, 1, 2, 3, 4, 5, 6, 7}));
    assert(b.uss == (vector<vector<int>>{{0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}}));
  }
  {
    Bisimulation b(3);
    b.ae(1, 2);
    b.ae(1, 2);
    b.ae(1, 2);
    b.ae(1, 2);
    b.ae(1, 2);
    b.ae(2, 1);
    b.ae(2, 1);
    b.ae(2, 1);
    b.ae(2, 1);
    b.ae(2, 1);
    b.run();
    assert(b.nn == 2);
    assert(b.ids == (vector<int>{0, 1, 1}));
    assert(b.uss == (vector<vector<int>>{{0}, {1, 2}}));
  }
  {
    // 0: [1, 2, 3], 1: [1, 2, 2], 2: [1, 1, 3], 3: [2, 2]
    Bisimulation b(9);
    b.ae(0, 1); b.ae(0, 2); b.ae(0, 4);
    b.ae(1, 1); b.ae(1, 5); b.ae(1, 7);
    b.ae(2, 1); b.ae(2, 1); b.ae(2, 8);
    b.ae(3, 1); b.ae(3, 5); b.ae(3, 8);
    b.ae(4, 2); b.ae(4, 5);
    b.ae(5, 1); b.ae(5, 1); b.ae(5, 4);
    b.ae(6, 1); b.ae(6, 2); b.ae(6, 8);
    b.ae(7, 1); b.ae(7, 1); b.ae(7, 4);
    b.ae(8, 5); b.ae(8, 5);
    b.run();
    assert(b.nn == 4);
    assert(b.ids == (vector<int>{0, 1, 2, 0, 3, 2, 0, 2, 3}));
    assert(b.uss == (vector<vector<int>>{{0, 3, 6}, {1}, {2, 5, 7}, {4, 8}}));
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
