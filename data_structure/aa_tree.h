#ifndef LIBRA_DATA_STRUCTURE_AA_TREE_H_
#define LIBRA_DATA_STRUCTURE_AA_TREE_H_

#include <assert.h>

////////////////////////////////////////////////////////////////////////////////
// leaf node: uncut interval
// internal node: concatenation of intervals for l and r (constitutes AA tree)
// T: monoid representing information of an interval.
//   T()  should return the identity.
//   T(S s)  should represent a single element of the array.
//   T::push(T &l, T &r)  should push the lazy update.
//   T::pull(const T &l, const T &r)  should pull two intervals.
// (in addition to T for SegmentTreeRange)
//   T::sz  should represent the length of the interval.
//   T::init(SignedInteger sz_)  should initialize an interval (for T()).
template <class T> struct AATree {
  using Size = decltype(T().sz);
  AATree *l, *r;
  int lev;
  T t;

  // Creates [0, sz).
  AATree(Size sz) : l(nullptr), r(nullptr), lev(0), t() {
    t.init(sz);
  }

  static void free(AATree *u) {
    if (!u) return;
    free(u->l);
    free(u->r);
    delete u;
  }

  inline Size sz() const {
    return t.sz;
  }
  inline void push() {
    t.push(l->t, r->t);
  }
  inline void pull() {
    t.pull(l->t, r->t);
  }

  //   v---u          v---u   //
  //  / \   \   ->   /   / \  //
  // o   o   o      o   o   o //
  static AATree *rotSkew(AATree *u) {
    if (!(u->l && u->lev == u->l->lev)) return u;
    AATree *v = u->l;
    u->l = v->r;
    u->pull();
    v->r = u;
    v->pull();
    return v;
  }
  //                      v   //
  //                     / \  //
  //   u---v---o        u   o //
  //  /   /       ->   / \    //
  // o   o            o   o   //
  static AATree *rotSplit(AATree *u) {
    if (!(u->r && u->r->r && u->lev == u->r->r->lev)) return u;
    AATree *v = u->r;
    u->r = v->l;
    u->pull();
    v->l = u;
    ++v->lev;
    v->pull();
    return v;
  }

  // Cuts at a.
  static void cut(AATree *&u, Size a) {
    if (a <= 0 || u->sz() <= a) return;
    if (!u->lev) {
      u->l = new AATree(a);
      u->r = new AATree(u->sz() - a);
      u->lev = 1;
      u->push();
      return;
    }
    u->push();
    if (a <= u->l->sz()) {
      cut(u->l, a);
      u->pull();
      u = rotSplit(rotSkew(u));
    } else {
      cut(u->r, a - u->l->sz());
      u->pull();
      u = rotSplit(rotSkew(u));
    }
  }

  // Applies T::f(args...) to [a, b).
  template <class F, class... Args> void ch(Size a, Size b, F f, Args &&... args) {
    if (b <= 0 || sz() <= a) return;
    if (a <= 0 && sz() <= b) {
      (t.*f)(args...);
      return;
    }
    push();
    l->ch(a, b, f, args...);
    r->ch(a - l->sz(), b - l->sz(), f, args...);
    pull();
  }

  // Calculates the product for [a, b).
  T get(Size a, Size b) {
    if (b <= 0 || sz() <= a) return T();
    if (a <= 0 && sz() <= b) return t;
    push();
    const T prodL = l->get(a, b);
    const T prodR = r->get(a - l->sz(), b - l->sz());
    T prod;
    prod.pull(prodL, prodR);
    return prod;
  }

  // Calculates T::f(args...) of a monoid type for [a, b).
  //   op(-, -)  should calculate the product.
  //   e()  should return the identity.
  template <class Op, class E, class F, class... Args>
#if __cplusplus >= 201402L
  auto
#else
  decltype((std::declval<T>().*F())())
#endif
  get(Size a, Size b, Op op, E e, F f, Args &&... args) {
    if (b <= 0 || sz() <= a) return e();
    if (a <= 0 && sz() <= b) return (t.*f)(args...);
    push();
    const auto prodL = l->get(a, b, op, e, f, args...);
    const auto prodR = r->get(a - l->sz(), b - l->sz(), op, e, f, args...);
    return op(prodL, prodR);
  }

  // TODO: findRight, findLeft
};
////////////////////////////////////////////////////////////////////////////////

#endif  // LIBRA_DATA_STRUCTURE_AA_TREE_H_
