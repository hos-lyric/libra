#ifndef LIBRA_ALGEBRA_MODINT_H_
#define LIBRA_ALGEBRA_MODINT_H_

#include <assert.h>
#include <ostream>
#include <utility>
#include <vector>

using std::ostream;
using std::pair;
using std::vector;

////////////////////////////////////////////////////////////////////////////////
// neighbors of u: [pt[u], pt[u + 1])
struct Graph {
  int n;
  vector<pair<int, int>> edges;
  vector<int> pt;
  vector<int> zu;
  int operator[](int j) const {
    return zu[j];
  }

  Graph() : n(0), edges() {}
  explicit Graph(int n_) : n(n_), edges() {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    edges.emplace_back(u, v);
  }
  void build(bool directed) {
    const int edgesLen = edges.size();
    pt.assign(n + 1, 0);
    if (directed) {
      for (int i = 0; i < edgesLen; ++i) {
        ++pt[edges[i].first];
      }
      for (int u = 0; u < n; ++u) pt[u + 1] += pt[u];
      zu.resize(edgesLen);
      for (int i = edgesLen; --i >= 0; ) {
        zu[--pt[edges[i].first]] = edges[i].second;
      }
    } else {
      for (int i = 0; i < edgesLen; ++i) {
        ++pt[edges[i].first];
        ++pt[edges[i].second];
      }
      for (int u = 0; u < n; ++u) pt[u + 1] += pt[u];
      zu.resize(2 * edgesLen);
      for (int i = edgesLen; --i >= 0; ) {
        const int u = edges[i].first, v = edges[i].second;
        zu[--pt[u]] = v;
        zu[--pt[v]] = u;
      }
    }
  }
  friend ostream &operator<<(ostream &os, const Graph &g) {
    os << "Graph(n=" << g.n << "; ";
    for (int u = 0; u < g.n; ++u) {
      if (u != 0) os << ", ";
      os << u << ":[";
      for (int j = g.pt[u]; j < g.pt[u + 1]; ++j) {
        if (j != g.pt[u]) os << ",";
        os << g[j];
      }
      os << "]";
    }
    os << ")";
    return os;
  }
};
////////////////////////////////////////////////////////////////////////////////

#endif  // LIBRA_ALGEBRA_MODINT_H_
