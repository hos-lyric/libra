#include <assert.h>
#include <utility>

using std::pair;
using std::swap;

// T: monoid representing information of an element and an interval.
//   T()  should return the identity.
//   T::push(T *l, T *r)  should push the lazy update.
//   T::pull(const Node *l, const Node *r)  should pull two intervals.
//     The node itself contains an element: This should calculate l * self * r.
//   T::operator<(const T &t)  is used for "Cmp" functions.
template <class T> struct Splay {
  Splay *p, *l, *r;
  T t;
  Splay() : p(nullptr), l(nullptr), r(nullptr), t() {}
  Splay(const T &t_) : p(nullptr), l(nullptr), r(nullptr), t(t_) {}
  void push() {
    t.push(l ? &l->t : nullptr, r ? &r->t : nullptr);
  }
  void pull() {
    t.pull(l ? &l->t : nullptr, r ? &r->t : nullptr);
  }
  void pushRec() {
    if (p) p->pushRec();
    push();
  }
  void rotate() {
    if (p->l == this) { if (r) { r->p = p; } p->l = r; r = p; }
    else              { if (l) { l->p = p; } p->r = l; l = p; }
    Splay *pp = p->p;
    if (pp) ((pp->l == p) ? pp->l : pp->r) = this;
    p->pull(); p->p = this; p = pp;
  }
  Splay *splay() {
    pushRec();
    for (; p; rotate()) if (p->p) ((p->l == this) == (p->p->l == p)) ? p->rotate() : rotate();
    pull();
    return this;
  }
  void linkL(Splay *a) {
    assert(!l);
    l = a; if (l) l->p = this;
    pull();
  }
  void linkR(Splay *a) {
    assert(!r);
    r = a; if (r) r->p = this;
    pull();
  }
  void linkLR(Splay *a, Splay *b) {
    assert(!l); assert(!r);
    l = a; if (l) l->p = this;
    r = b; if (r) r->p = this;
    pull();
  }
  void cutL() {
    if (l) l->p = nullptr;
    l = nullptr;
    pull();
  }
  void cutR() {
    if (r) r->p = nullptr;
    r = nullptr;
    pull();
  }
  void cutLR() {
    if (l) l->p = nullptr;
    if (r) r->p = nullptr;
    l = r = nullptr;
    pull();
  }
  // Splays the leftmost node.
  Splay *leftmost() {
    Splay *a = this;
    for (; a->l; a = a->l) {}
    return a->splay();
  }
  // Splays the rightmost node.
  Splay *rightmost() {
    Splay *a = this;
    for (; a->r; a = a->r) {}
    return a->splay();
  }
  // Iterates the tree, calling f on each node.
  template <class F> void dfs(F f) {
    push();
    if (l) l->dfs(f);
    f(this);
    if (r) r->dfs(f);
  }
  // Concatenates two trees.
  friend Splay *concat(Splay *a, Splay *b) {
    if (!a) return b;
    if (!b) return a;
    a = a->rightmost();
    a->linkR(b);
    return a;
  }
  // Splays the k-th element.
  Splay *at(int k) {
    assert(0 <= k); assert(k < t.size);
    for (Splay *a = this; ; ) {
      const int sizeL = a->l ? a->l->t.size : 0;
      if (k < sizeL) {
        a = a->l;
      } else if (k == sizeL) {
        return a->splay();
      } else {
        a = a->r;
        k -= (sizeL + 1);
      }
    }
  }
  // Splits the tree by size: [0, k), [k, a->size).
  friend pair<Splay *, Splay *> splitAt(Splay *a, int k) {
    assert(0 <= k); assert(k <= (a ? a->t.size : 0));
    if (k == 0) return std::make_pair(nullptr, a);
    if (k == a->t.size) return std::make_pair(a, nullptr);
    a = a->at(k);
    Splay *l = a->l;
    a->cutL();
    return std::make_pair(l, a);
  }
  // Splits the tree by operator<: (< target), (>= target).
  // Splays the rightmost (< target) and the leftmost (>= target).
  friend pair<Splay *, Splay *> splitCmp(Splay *a, const T &target) {
    Splay *l = nullptr, *r = nullptr;
    for (; a; ) {
      a->push();
      if (a->t < target) {
        l = a;
        a = a->r;
      } else {
        r = a;
        a = a->l;
      }
    }
    if (l) {
      l->splay();
      l->cutR();
    }
    if (r) r->splay();
    return std::make_pair(l, r);
  }
  // Inserts b into the tree, using T::operator<.
  friend void insertCmp(Splay *&a, Splay *b) {
    auto s = splitCmp(a, b->t);
    b->linkLR(s.first, s.second);
    a = b;
  }
  // Inserts b's nodes into the tree one by one, using T::operator<.
  friend void meldRecCmp(Splay *&a, Splay *b) {
    if (!b) return;
    Splay *l = b->l, *r = b->r;
    b->push();
    b->cutLR();
    meldRecCmp(a, l);
    insertCmp(a, b);
    meldRecCmp(a, r);
  }
  // Meld two trees, using T::operator<.
  friend Splay *meldCmp(Splay *a, Splay *b) {
    if (!a) return b;
    if (!b) return a;
    if (a->t.size < b->t.size) swap(a, b);
    meldRecCmp(a, b);
    return a;
  }
  // Cuts out [kL, kR) of the tree and calls f.
  template <class F> friend void range(Splay *&a, int kL, int kR, F f) {
    assert(0 <= kL); assert(kL <= kR); assert(kR <= (a ? a->t.size : 0));
    if (kL == kR) { f(nullptr); return; }
    Splay *b = nullptr;
    if (kR < a->t.size) {
      b = a->at(kR);
      a = b->l;
      b->cutL();
    }
    if (0 < kL) a = a->at(kL - 1)->r;
    f(a);
    if (b) b->linkL(a->splay());
    a->splay();
  }
  // Applies T::f(args...) to [kL, kR).
  template <class F, class... Args>
  friend void ch(Splay *&a, int kL, int kR, F f, Args &&... args) {
    range(a, kL, kR, [&](Splay *b) -> void { if (b) (b->t.*f)(args...); });
  }
  // Calculates the product for [kL, kR).
  friend T get(Splay *&a, int kL, int kR) {
    T t;
    range(a, kL, kR, [&](Splay *b) -> void { if (b) t = b->t; });
    return t;
  }
};

struct Node {
  int size;
  Node() : size(0) {}
  void push(Node *l, Node *r) {}
  void pull(const Node *l, const Node *r) {
    size = (l ? l->size : 0) + 1 + (r ? r->size : 0);
  }
  bool operator<(const Node &t) {
    return false;
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <algorithm>
#include <iostream>
#include <vector>

using std::cerr;
using std::endl;
using std::min;
using std::vector;

void unittest() {
  // TODO
}

// https://judge.yosupo.jp/problem/dynamic_sequence_range_affine_range_sum
namespace yosupo_dynamic_sequence_range_affine_range_sum {
constexpr unsigned MO = 998244353;
struct Node {
  int size;
  unsigned val, sum, lzB, lzC;
  Node() : size(0), val(0), sum(0), lzB(1), lzC(0) {}
  Node(unsigned val_) : size(1), val(val_), sum(val_), lzB(1), lzC(0) {}
  void push(Node *l, Node *r) {
    if (l) l->apply(lzB, lzC);
    if (r) r->apply(lzB, lzC);
    lzB = 1; lzC = 0;
  }
  void pull(const Node *l, const Node *r) {
    size = (l ? l->size : 0) + 1 + (r ? r->size : 0);
    sum = ((l ? l->sum : 0) + val + (r ? r->sum : 0)) % MO;
  }
  void apply(unsigned long long b, unsigned long long c) {
    val = (b * val + c) % MO;
    sum = (b * sum + c * size) % MO;
    lzB = (b * lzB) % MO;
    lzC = (b * lzC + c) % MO;
  }
};
void run() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    int numNodes = 0;
    vector<Splay<Node>> nodes((N + Q) << 1);
    auto newNode = [&](unsigned val) -> Splay<Node> * {
      return &(nodes[numNodes++] = Node(val));
    };
    Splay<Node> *seg0 = nullptr, *seg1 = nullptr;
    for (int i = 0; i < N; ++i) {
      unsigned A;
      scanf("%u", &A);
      seg0 = concat(seg0, newNode(A));
      seg1 = concat(newNode(A), seg1);
    }
    int n = N;
    for (int q = 0; q < Q; ++q) {
      int O;
      scanf("%d", &O);
      switch (O) {
        case 0: {
          // insert
          int I;
          unsigned X;
          scanf("%d%u", &I, &X);
          auto res0 = splitAt(seg0, I);
          seg0 = concat(concat(res0.first, newNode(X)), res0.second);
          auto res1 = splitAt(seg1, n - I);
          seg1 = concat(concat(res1.first, newNode(X)), res1.second);
          ++n;
        } break;
        case 1: {
          // erase
          int I;
          scanf("%d", &I);
          assert(0 <= I); assert(I < n);
          auto res0 = splitAt(seg0, I);
          auto res0R = splitAt(res0.second, 1);
          seg0 = concat(res0.first, res0R.second);
          auto res1 = splitAt(seg1, n - 1 - I);
          auto res1R = splitAt(res1.second, 1);
          seg1 = concat(res1.first, res1R.second);
          --n;
        } break;
        case 2: {
          // reverse
          int L, R;
          scanf("%d%d", &L, &R);
          auto res0 = splitAt(seg0, R);
          auto res0L = splitAt(res0.first, L);
          auto res1 = splitAt(seg1, n - L);
          auto res1L = splitAt(res1.first, n - R);
          seg0 = concat(concat(res0L.first, res1L.second), res0.second);
          seg1 = concat(concat(res1L.first, res0L.second), res1.second);
        } break;
        case 3: {
          // apply
          int L, R;
          unsigned B, C;
          scanf("%d%d%u%u", &L, &R, &B, &C);
          ch(seg0, L, R, &Node::apply, B, C);
          ch(seg1, n - R, n - L, &Node::apply, B, C);
        } break;
        case 4: {
          // sum
          int L, R;
          scanf("%d%d", &L, &R);
          const Node res = get(seg0, L, R);
          printf("%u\n", res.sum);
        } break;
        default: assert(false);
      }
    }
  }
}
}  // yosupo_dynamic_sequence_range_affine_range_sum

namespace qoj7961 {
// dp[u]: convex function on [0, sz[u]]
// dp[u] = 0_[0,1] * *[v] (|K - 2 x| + dp[v])
//   *: min-plus convolution
struct Node {
  int size;
  int val, lz;
  Node() : size(0), val(0), lz(0) {}
  Node(int val_) : size(1), val(val_), lz(0) {}
  void push(Node *l, Node *r) {
    if (l) l->add(lz);
    if (r) r->add(lz);
    lz = 0;
  }
  void pull(const Node *l, const Node *r) {
    size = (l ? l->size : 0) + 1 + (r ? r->size : 0);
  }
  void add(int a) {
    val += a;
    lz += a;
  }
  bool operator<(const Node &t) {
    return (val < t.val);
  }
};
int N, K;
vector<int> A, B;
vector<vector<int>> graph;
vector<Splay<Node>> nodes;
Splay<Node> *solve(int u, int p) {
  auto ret = &(nodes[u] = Node(0));
  for (const int v : graph[u]) if (p != v) {
    auto res = solve(v, u);
    ch(res, 0, min(K/2, res->t.size), &Node::add, -2);
    if ((K+1)/2 < res->t.size) ch(res, (K+1)/2, res->t.size, &Node::add, +2);
    ret = meldCmp(ret, res);
  }
  return ret;
}
void run() {
  for (; ~scanf("%d%d", &N, &K); ) {
    A.resize(N - 1);
    B.resize(N - 1);
    for (int i = 0; i < N - 1; ++i) {
      scanf("%d%d", &A[i], &B[i]);
      --A[i];
      --B[i];
    }
    graph.assign(N, {});
    for (int i = 0; i < N - 1; ++i) {
      graph[A[i]].push_back(B[i]);
      graph[B[i]].push_back(A[i]);
    }
    nodes.resize(N);
    auto res = solve(0, -1);
    long long ans = static_cast<long long>(N - 1) * K;
    int k = 0;
    res->dfs([&](const Splay<Node> *a) -> void {
      if (k++ < K) ans += a->t.val;
    });
    printf("%lld\n", ans);
  }
}
}  // qoj7961

namespace qoj5421 {
// dp[u]: concave function on [0, sz[u]]
// dp[u] = 0_[0,1] * *[v] (x (K - x) + dp[v])
//   *: max-plus convolution
struct Node {
  int size, sizeL;
  // += (a + d k)
  long long val, lzA, lzD;
  Node() : size(0), sizeL(0), val(0), lzA(0), lzD(0) {}
  Node(long long val_) : size(1), sizeL(0), val(val_), lzA(0), lzD(0) {}
  void push(Node *l, Node *r) {
    if (l) l->add(lzA, lzD);
    if (r) r->add(lzA + lzD * (sizeL + 1), lzD);
    lzA = lzD = 0;
  }
  void pull(const Node *l, const Node *r) {
    size = (l ? l->size : 0) + 1 + (r ? r->size : 0);
    sizeL = (l ? l->size : 0);
  }
  void add(long long a, long long d) {
    val += (a + d * sizeL);
    lzA += a;
    lzD += d;
  }
  // decreasing
  bool operator<(const Node &t) {
    return (val > t.val);
  }
};
int N, K;
vector<int> A, B;
vector<long long> C;
vector<vector<int>> G;
vector<Splay<Node>> nodes;
Splay<Node> *solve(int u, int p) {
  auto ret = &(nodes[u] = Node(0));
  for (const int i : G[u]) {
    const int v = A[i] ^ B[i] ^ u;
    if (p != v) {
      auto res = solve(v, u);
      ch(res, 0, res->t.size, &Node::add, C[i] * (K - 1), C[i] * -2);
      ret = meldCmp(ret, res);
    }
  }
  return ret;
}
void run() {
  for (; ~scanf("%d%d", &N, &K); ) {
    A.resize(N - 1);
    B.resize(N - 1);
    C.resize(N - 1);
    for (int i = 0; i < N - 1; ++i) {
      scanf("%d%d%lld", &A[i], &B[i], &C[i]);
      --A[i];
      --B[i];
    }
    G.assign(N, {});
    for (int i = 0; i < N - 1; ++i) {
      G[A[i]].push_back(i);
      G[B[i]].push_back(i);
    }
    nodes.resize(N);
    auto res = solve(0, -1);
    long long ans = 0;
    int k = 0;
    res->dfs([&](const Splay<Node> *a) -> void {
      if (k++ < K) ans += a->t.val;
    });
    printf("%lld\n", ans);
  }
}
}  // qoj5421

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupo_dynamic_sequence_range_affine_range_sum::run();
  // qoj7961::run();
  // qoj5421::run();
  return 0;
}
