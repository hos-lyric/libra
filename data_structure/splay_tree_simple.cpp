#include <assert.h>
#include <utility>

using std::pair;

// TODO: usage different from Splay

template <class T> struct SplaySimple {
  SplaySimple *p, *l, *r;
  T t;
  SplaySimple() : p(nullptr), l(nullptr), r(nullptr), t() {}
  void rotate() {
    if (p->l == this) { if (r) { r->p = p; } p->l = r; r = p; }
    else              { if (l) { l->p = p; } p->r = l; l = p; }
    SplaySimple *pp = p->p;
    if (pp) ((pp->l == p) ? pp->l : pp->r) = this;
    p->p = this; p = pp;
  }
  SplaySimple *splay() {
    for (; p; rotate()) if (p->p) ((p->l == this) == (p->p->l == p)) ? p->rotate() : rotate();
    return this;
  }
  SplaySimple *linkL(SplaySimple *a) { assert(!l); l = a; if (l) { l->p = this; } return this; }
  SplaySimple *linkR(SplaySimple *a) { assert(!r); r = a; if (r) { r->p = this; } return this; }
  SplaySimple *cutL() { if (l) { l->p = nullptr; l = nullptr; } return this; }
  SplaySimple *cutR() { if (r) { r->p = nullptr; r = nullptr; } return this; }
  SplaySimple *leftmost() {
    SplaySimple *a = this;
    for (; a->l; a = a->l) {}
    return a->splay();
  }
  SplaySimple *rightmost() {
    SplaySimple *a = this;
    for (; a->r; a = a->r) {}
    return a->splay();
  }
  template <class F> void dfs(F f) {
    if (l) l->dfs(f);
    f(this);
    if (r) r->dfs(f);
  }
  friend SplaySimple *concat(SplaySimple *a, SplaySimple *b) {
    if (!a) return b;
    if (!b) return a;
    return a->splay()->rightmost()->linkR(b->splay());
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <vector>

using std::cerr;
using std::endl;
using std::vector;

void unittest() {
  vector<SplaySimple<int>> nodes(10);
  for (int u = 0; u < 10; ++u) nodes[u].t = 100 + u;
  auto test = [&](int i, const vector<int> &expected) -> void {
    vector<int> actual;
    nodes[i].dfs([&](SplaySimple<int> *a) -> void {
      actual.push_back(a->t);
    });
    assert(expected == actual);
  };
  test(0, {100});
  concat(concat(&nodes[1], &nodes[3]), concat(&nodes[2], &nodes[4]));
  nodes[2].splay();
  test(2, {101, 103, 102, 104});
  concat(&nodes[5], concat(&nodes[6], &nodes[7]));
  concat(&nodes[4], &nodes[7]);
  test(7, {105, 106, 107});
  nodes[7].splay();
  test(7, {101, 103, 102, 104, 105, 106, 107});
  nodes[4].splay()->cutL();
  nodes[4].splay()->cutL();
  test(4, {104, 105, 106, 107});
  nodes[1].splay();
  test(1, {101, 103, 102});
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
