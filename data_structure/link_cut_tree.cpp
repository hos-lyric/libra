#include <utility>

using std::swap;

// Dynamically decomposes a rooted tree into paths.
//   solid/dashed: similar to heavy/light in HLD
//   Maintains each solid path by a splay tree, left/right: root/leaf side.
//   p: pointer in a splay tree, or parent via dashed edge
// T: commutative monoid
//   T::operator+(const T &l, const T &r)  should return l + r.
template <class T> struct LinkCutTree {
  LinkCutTree *p, *l, *r;
  bool rev;
  T t, sum;
  LinkCutTree() : p(nullptr), l(nullptr), r(nullptr), rev(false), t(), sum() {}
  explicit LinkCutTree(const T &t_) : p(nullptr), l(nullptr), r(nullptr), rev(false), t(t_), sum(t_) {}
  void push() {
    if (rev) {
      if (l) l->reverse();
      if (r) r->reverse();
    }
    rev = false;
  }
  void pull() {
    sum = l ? (r ? (l->sum + t + r->sum) : (l->sum + t)) : (r ? (t + r->sum) : t);
  }
  void reverse() {
    rev = !rev;
    swap(l, r);
  }
  bool isRoot() const {
    return (!p || (p->l != this && p->r != this));
  }
  void pushRec() {
    if (!isRoot()) p->pushRec();
    push();
  }
  void rotateR() {
    if (r) r->p = p;
    p->l = r; r = p;
    LinkCutTree *pp = p->p;
    if (pp) {
           if (pp->l == p) { pp->l = this; }
      else if (pp->r == p) { pp->r = this; }
    }
    p->pull(); p->p = this; p = pp;
  }
  void rotateL() {
    if (l) l->p = p;
    p->r = l; l = p;
    LinkCutTree *pp = p->p;
    if (pp) {
           if (pp->l == p) { pp->l = this; }
      else if (pp->r == p) { pp->r = this; }
    }
    p->pull(); p->p = this; p = pp;
  }
  void splay() {
    pushRec();
    for (; ; ) {
      if (isRoot()) {
        break;
      } else if (p->isRoot()) {
        if (p->l == this) { rotateR(); } else { rotateL(); }
        break;
      } else {
        if (p->l == this) {
          if (p->p->l == p) { p->rotateR(); rotateR(); } else { rotateR(); rotateL(); }
        } else {
          if (p->p->l == p) { rotateL(); rotateR(); } else { p->rotateL(); rotateL(); }
        }
      }
    }
    pull();
  }
  // Makes the path from this to the root solid.
  //   Makes all incident solid edges below this dashed.
  // Returns the vertex where it entered the last existing solid path.
  LinkCutTree *expose() {
    LinkCutTree *u = this, *v = nullptr;
    for (; u; u = u->p) { u->splay(); u->r = v; u->pull(); v = u; }
    splay();
    return v;
  }
  // (parent of this) := u
  void link(LinkCutTree *u) {
    expose(); u->expose(); p = u; u->r = this; u->pull();
  }
  // (parent of this) := null
  void cut() {
    expose(); l->p = nullptr; l = nullptr; pull();
  }
  // Makes this as the root of the tree.
  void evert() {
    expose(); reverse();
  }
  // Returns the root of the tree this belongs.
  LinkCutTree *root() {
    expose();
    for (LinkCutTree *u = this; ; u = u->l) if (!u->l) { u->splay(); return u; }
  }
  // Returns LCA of this and u.
  LinkCutTree *lca(LinkCutTree *u) {
    expose(); return u->expose();
  }
  // Returns the sum of the values on the this-u path.
  T pathSum(LinkCutTree *u) {
    expose();
    LinkCutTree *v = u->expose();
    splay(); v->splay();
    const T sumU = v->r ? (v->t + v->r->sum) : v->t;
    return (v == this) ? sumU : ((l ? (l->sum + t) : t) + sumU);
  }
};  // LinkCutTree<T>

////////////////////////////////////////////////////////////////////////////////

#include <assert.h>
#include <stdio.h>
#include <iostream>
#include <queue>
#include <random>
#include <vector>

using std::cerr;
using std::endl;
using std::queue;
using std::mt19937_64;
using std::vector;

struct Brute {
  int n;
  vector<int> par;
  vector<unsigned long long> values;
  Brute(int n_) : n(n_), par(n, -1), values(n, 0) {}
  void link(int u, int p) {
    assert(!~par[u]);
    assert(u != root(p));
    par[u] = p;
  }
  void cut(int u) {
    assert(~par[u]);
    par[u] = -1;
  }
  void evert(int r) {
    vector<vector<int>> graph(n);
    for (int u = 0; u < n; ++u) if (~par[u]) {
      graph[par[u]].push_back(u);
      graph[u].push_back(par[u]);
    }
    queue<int> que;
    par[r] = -1;
    que.push(r);
    for (; que.size(); ) {
      const int u = que.front();
      que.pop();
      for (const int v : graph[u]) if (par[u] != v) {
        par[v] = u;
        que.push(v);
      }
    }
  }
  int root(int u) const {
    for (; ~par[u]; u = par[u]) {}
    return u;
  }
  int lca(int u, int v) const {
    vector<int> xs, ys;
    for (int x = u; ~x; x = par[x]) xs.push_back(x);
    for (int x = v; ~x; x = par[x]) ys.push_back(x);
    assert(xs.back() == ys.back());
    int l = -1;
    for (; xs.size() && ys.size() && xs.back() == ys.back(); xs.pop_back(), ys.pop_back()) l = xs.back();
    return l;
  }
  unsigned long long pathSum(int u, int v) const {
    vector<int> xsU, xsV;
    for (int x = u; ~x; x = par[x]) xsU.push_back(x);
    for (int x = v; ~x; x = par[x]) xsV.push_back(x);
    assert(xsU.back() == xsV.back());
    int l = -1;
    for (; xsU.size() && xsV.size() && xsU.back() == xsV.back(); xsU.pop_back(), xsV.pop_back()) {
      l = xsU.back();
    }
    unsigned long long sum = values[l];
    for (const int x : xsU) sum += values[x];
    for (const int x : xsV) sum += values[x];
    return sum;
  }
};  // Brute

void unittest() {
  {
    using LCT = LinkCutTree<int>;
    LCT *us[6];
    for (int e = 0; e < 6; ++e) us[e] = new LCT(1 << e);
    auto id = [&](LCT *u) -> int {
      if (!u) return -1;
      for (int e = 0; e < 6; ++e) if (u == us[e]) return e;
      assert(false);
    };
    auto debug = [&]() -> void {
      for (int e = 0; e < 6; ++e) {
        fprintf(stderr, "us[%d]: p = %2d, l = %2d, r = %2d, rev = %d, t = %2d, sum = %2d = ",
                e, id(us[e]->p), id(us[e]->l), id(us[e]->r), us[e]->rev, us[e]->t, us[e]->sum);
        for (int ee = 0; ee < 6; ++ee) fprintf(stderr, "%d", us[e]->sum >> ee & 1);
        fprintf(stderr, "\n");
      }
      fprintf(stderr, "\n");
      fflush(stderr);
    };
    us[1]->link(us[0]);
    us[4]->link(us[0]);
    us[2]->link(us[1]);
    us[3]->link(us[1]);
    us[5]->link(us[4]);
    // 0 {1 {2, 3}, 4 {5} }
    debug();
    assert(us[0]->root() == us[0]);
    assert(us[5]->root() == us[0]);
    assert(us[2]->lca(us[3]) == us[1]);
    assert(us[2]->lca(us[5]) == us[0]);
    assert(us[1]->lca(us[2]) == us[1]);
    assert(us[4]->lca(us[5]) == us[4]);
    assert(us[2]->pathSum(us[3]) == 14);
    assert(us[2]->pathSum(us[5]) == 55);
    assert(us[1]->pathSum(us[3]) == 10);
    assert(us[0]->pathSum(us[5]) == 49);
    us[3]->evert();
    // 3 {1 {0 {4 {5}}, 2}}
    debug();
    assert(us[0]->root() == us[3]);
    assert(us[0]->pathSum(us[3]) == 11);
    us[0]->evert();
    // 0 {1 {2, 3}, 4 {5} }
    debug();
    us[1]->cut();
    // 0 {4 {5}}, 1 {2, 3}
    debug();
    assert(us[1]->root() == us[1]);
    assert(us[2]->root() == us[1]);
    assert(us[3]->root() == us[1]);
    assert(us[4]->root() == us[0]);
    assert(us[5]->root() == us[0]);
    assert(us[2]->pathSum(us[3]) == 14);
    assert(us[4]->pathSum(us[5]) == 48);
    us[1]->link(us[0]);
    // 0 {1 {2, 3}, 4 {5} }
    debug();
    assert(us[5]->root() == us[0]);
    assert(us[3]->pathSum(us[5]) == 59);
    for (int e = 0; e < 6; ++e) delete us[e];
  }
  for (int N = 1; N <= 100; ++N) {
    using LCT = LinkCutTree<unsigned long long>;
    mt19937_64 rng(0);
    Brute brt(N);
    vector<LCT *> nodes(N);
    for (int u = 0; u < N; ++u) nodes[u] = new LCT();
    for (int q = 0; q < 10'000; ++q) {
      switch (rng() % 7) {
        case 0: {
          // link
          vector<int> us;
          for (int u = 0; u < N; ++u) if (!~brt.par[u]) us.push_back(u);
          if (us.size() >= 2) {
            const int u = us[rng() % us.size()];
            for (int v = rng() % N; ; ++v %= N) if (u != brt.root(v)) {
              brt.link(u, v);
              nodes[u]->link(nodes[v]);
              break;
            }
          }
        } break;
        case 1: {
          // cut
          vector<int> us;
          for (int u = 0; u < N; ++u) if (~brt.par[u]) us.push_back(u);
          if (us.size()) {
            const int u = us[rng() % us.size()];
            brt.cut(u);
            nodes[u]->cut();
          }
        } break;
        case 2: {
          // evert
          const int r = rng() % N;
          brt.evert(r);
          nodes[r]->evert();
        } break;
        case 3: {
          // root
          const int u = rng() % N;
          assert(nodes[brt.root(u)] == nodes[u]->root());
        } break;
        case 4: {
          // lca
          const int u = rng() % N;
          const int r = brt.root(u);
          for (int v = rng() % N; ; ++v %= N) if (r == brt.root(v)) {
            assert(nodes[brt.lca(u, v)] == nodes[u]->lca(nodes[v]));
            break;
          }
        } break;
        case 5: {
          // pathSum
          const int u = rng() % N;
          const int r = brt.root(u);
          for (int v = rng() % N; ; ++v %= N) if (r == brt.root(v)) {
            assert(brt.pathSum(u, v) == nodes[u]->pathSum(nodes[v]));
            break;
          }
        } break;
        case 6: {
          const int u = rng() % N;
          const unsigned long long t = rng();
          brt.values[u] = t;
          nodes[u]->expose();
          nodes[u]->t = brt.values[u];
          nodes[u]->pull();
        } break;
        default: assert(false);
      }
    }
    for (int u = 0; u < N; ++u) delete nodes[u];
    cerr << "[unittest] PASSED N = " << N << endl;
  }
}  // unittest

// https://judge.yosupo.jp/problem/dynamic_tree_vertex_add_path_sum
void yosupo_dynamic_tree_vertex_add_path_sum() {
  using LCT = LinkCutTree<long long>;
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    vector<LCT> nodes(N);
    for (int u = 0; u < N; ++u) {
      long long A;
      scanf("%lld", &A);
      nodes[u] = LCT(A);
    }
    for (int i = 0; i < N - 1; ++i) {
      int U, V;
      scanf("%d%d", &U, &V);
      nodes[U].evert();
      nodes[U].link(&nodes[V]);
    }
    for (int q = 0; q < Q; ++q) {
      int O;
      scanf("%d", &O);
      if (O == 0) {
        int U, V, W, X;
        scanf("%d%d%d%d", &U, &V, &W, &X);
        nodes[U].evert();
        nodes[V].cut();
        nodes[W].evert();
        nodes[W].link(&nodes[X]);
      } else if (O == 1) {
        int U;
        long long A;
        scanf("%d%lld", &U, &A);
        nodes[U].expose();
        nodes[U].t += A;
        nodes[U].pull();
      } else if (O == 2) {
        int U, V;
        scanf("%d%d", &U, &V);
        const long long ans = nodes[U].pathSum(&nodes[V]);
        printf("%lld\n", ans);
      } else {
        assert(false);
      }
    }
  }
}  // yosupo_dynamic_tree_vertex_add_path_sum

// https://judge.yosupo.jp/problem/incremental_minimum_spanning_forest
namespace yosupo_incremental_minimum_spanning_forest {
// max weight
constexpr int INF = 1001001001;
struct Data {
  int weight;
  int id;
  Data() : weight(-INF), id(-1) {}
  Data(int weight_, int id_) : weight(weight_), id(id_) {}
};
Data operator+(const Data &l, const Data &r) {
  return (l.weight >= r.weight) ? l : r;
}
void run() {
  using LCT = LinkCutTree<Data>;
  int N, M;
  for (; ~scanf("%d%d", &N, &M); ) {
    vector<int> U(M), V(M), W(M);
    for (int i = 0; i < M; ++i) scanf("%d%d%d", &U[i], &V[i], &W[i]);
    vector<LCT> nodes(N + M);
    for (int i = 0; i < M; ++i) nodes[N + i] = LCT(Data(W[i], i));
    vector<int> ans(M, -1);
    for (int i = 0; i < M; ++i) {
      if (nodes[U[i]].root() != nodes[V[i]].root()) {
        nodes[V[i]].evert();
        nodes[V[i]].link(&nodes[N + i]);
        nodes[N + i].link(&nodes[U[i]]);
      } else {
        const Data mx = nodes[U[i]].pathSum(&nodes[V[i]]);
        if (mx.weight > W[i]) {
          const int j = mx.id;
          ans[i] = j;
          nodes[U[j]].evert();
          nodes[N + j].cut();
          nodes[V[j]].cut();
          nodes[V[i]].evert();
          nodes[V[i]].link(&nodes[N + i]);
          nodes[N + i].link(&nodes[U[i]]);
        } else {
          ans[i] = i;
        }
      }
    }
    for (int i = 0; i < M; ++i) {
      if (i) printf(" ");
      printf("%d", ans[i]);
    }
    puts("");
  }
}
}  // yosupo_incremental_minimum_spanning_forest

int main() {
  // unittest(); cerr << "PASSED unittest" << endl;
  // yosupo_dynamic_tree_vertex_add_path_sum();
  yosupo_incremental_minimum_spanning_forest::run();
  return 0;
}
