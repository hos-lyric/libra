#ifndef LIBRA_OTHER_MIN_BST_H_
#define LIBRA_OTHER_MIN_BST_H_

#include <assert.h>
#include <algorithm>
#include <queue>
#include <utility>
#include <vector>

using std::min;
using std::pair;
using std::priority_queue;
using std::swap;
using std::vector;

////////////////////////////////////////////////////////////////////////////////
template <class T, bool RECOVER> struct MinBST;

// Assumes as[i] >= 0.
// T: total and (2 inf) must not overflow
//   going up two nodes from non-leaf ==> weight at least doubled
template <class T> struct MinBST<T, /*RECOVER=*/false> {
  int n;
  T inf, total;
  explicit MinBST(const vector<T> &as) : n(as.size()), inf(1), total(0) {
    assert(n >= 1);
    for (int i = 0; i < n; ++i) if (as[i] > 0) inf += as[i];
    vector<T> bs(n + 2), cs(n + 1);
    vector<Heap> nodes(n - 1);
    vector<Heap *> heaps(n + 1, nullptr);
    vector<int> lef(n + 2), rig(n + 1);
    using Entry = pair<T, int>;
    priority_queue<Entry, vector<Entry>, std::greater<Entry>> que;
    bs[0] = bs[n + 1] = inf;
    for (int i = 0; i < n; ++i) bs[i + 1] = as[i];
    for (int i = 0; i < n + 1; ++i) {
      lef[i] = i - 1;
      rig[i] = i + 1;
      que.emplace(cs[i] = bs[i] + bs[i + 1], i);
    }
    auto merge = [&](int i, int j) -> int {
      heaps[i] = meld(heaps[i], heaps[j]);
      cs[j] = inf;
      return lef[rig[i] = rig[j]] = i;  // can modify lef[n + 1]
    };
    for (int k = 0; k < n - 1; ++k) {
      for (; ; ) {
        const T c = que.top().first;
        int i = que.top().second;
        que.pop();
        if (c == cs[i]) {
          total += c;
          bool leafL = false, leafR = false;
          // TODO: proof for tie-breaking
          if (heaps[i] && c == bs[i] + heaps[i]->val) {
            leafL = true;
            pop(heaps[i]);
          } else if (c == bs[i] + bs[rig[i]]) {
            leafL = leafR = true;
          } else {
            const T t = heaps[i]->val;
            pop(heaps[i]);
            if (heaps[i] && c == t + heaps[i]->val) {
              pop(heaps[i]);
            } else {
              leafR = true;
            }
          }
          if (leafL) i = merge(lef[i], i);
          if (leafR) i = merge(i, rig[i]);
          nodes[k].val = c;
          heaps[i] = meld(heaps[i], &nodes[k]);
          que.emplace(cs[i] = min({
            bs[i] + bs[rig[i]],
            min(bs[i], bs[rig[i]]) + heaps[i]->val,
            heaps[i]->val + secondMin(heaps[i]),
          }), i);
          break;
        }
      }
    }
  }

  // min skew heap
  struct Heap {
    Heap *l, *r;
    T val;
    Heap() : l(nullptr), r(nullptr), val(0) {}
  };
  Heap *meld(Heap *a, Heap *b) {
    if (!a) return b;
    if (!b) return a;
    if (a->val > b->val) swap(a, b);
    a->r = meld(a->r, b);
    swap(a->l, a->r);
    return a;
  }
  void pop(Heap *&a) {
    a = meld(a->l, a->r);
  }
  T secondMin(const Heap *a) {
    return a->l ? (a->r ? min(a->l->val, a->r->val) : a->l->val) : (a->r ? a->r->val : inf);
  }
};

// Assumes as[i] >= 0.
// T: total and (2 inf) must not overflow
//   going up two nodes from non-leaf ==> weight at least doubled
// ls[k], rs[k]: children of node (n + k)  (0 <= k < n - 1)
// dep[u]: depth of node u  (0 <= u < 2 n - 1)
template <class T> struct MinBST<T, /*RECOVER=*/true> {
  int n;
  T inf, total;
  vector<int> ls, rs;
  vector<int> dep;
  explicit MinBST(const vector<T> &as) : n(as.size()), inf(1), total(0) {
    assert(n >= 1);
    for (int i = 0; i < n; ++i) if (as[i] > 0) inf += as[i];
    vector<T> bs(n + 2), cs(n + 1);
    vector<Heap> nodes(n - 1);
    vector<Heap *> heaps(n + 1, nullptr);
    vector<int> lef(n + 2), rig(n + 1);
    using Entry = pair<T, int>;
    priority_queue<Entry, vector<Entry>, std::greater<Entry>> que;
    bs[0] = bs[n + 1] = inf;
    for (int i = 0; i < n; ++i) bs[i + 1] = as[i];
    for (int i = 0; i < n + 1; ++i) {
      lef[i] = i - 1;
      rig[i] = i + 1;
      que.emplace(cs[i] = bs[i] + bs[i + 1], i);
    }
    auto merge = [&](int i, int j) -> int {
      heaps[i] = meld(heaps[i], heaps[j]);
      cs[j] = inf;
      return lef[rig[i] = rig[j]] = i;  // can modify lef[n + 1]
    };
    ls.resize(n - 1);
    rs.resize(n - 1);
    for (int k = 0; k < n - 1; ++k) {
      for (; ; ) {
        const T c = que.top().first;
        int i = que.top().second;
        que.pop();
        if (c == cs[i]) {
          total += c;
          bool leafL = false, leafR = false;
          // TODO: proof for tie-breaking
          if (heaps[i] && c == bs[i] + heaps[i]->val) {
            leafL = true;
            ls[k] = i - 1;
            rs[k] = heaps[i]->id;
            pop(heaps[i]);
          } else if (c == bs[i] + bs[rig[i]]) {
            leafL = leafR = true;
            ls[k] = i - 1;
            rs[k] = rig[i] - 1;
          } else {
            const T t = heaps[i]->val;
            ls[k] = heaps[i]->id;
            pop(heaps[i]);
            if (heaps[i] && c == t + heaps[i]->val) {
              rs[k] = heaps[i]->id;
              pop(heaps[i]);
            } else {
              leafR = true;
              rs[k] = rig[i] - 1;
            }
          }
          if (leafL) i = merge(lef[i], i);
          if (leafR) i = merge(i, rig[i]);
          nodes[k].val = c;
          nodes[k].id = n + k;
          heaps[i] = meld(heaps[i], &nodes[k]);
          que.emplace(cs[i] = min({
            bs[i] + bs[rig[i]],
            min(bs[i], bs[rig[i]]) + heaps[i]->val,
            heaps[i]->val + secondMin(heaps[i]),
          }), i);
          break;
        }
      }
    }
    dep.resize(2 * n - 1);
    dep[2 * n - 2] = 0;
    for (int k = n - 1; --k >= 0; ) dep[ls[k]] = dep[rs[k]] = dep[n + k] + 1;
    vector<int> stack(n);
    for (int k = 0, i = 0; i < n; ++i) {
      int u = i;
      for (; i - k > 0 && dep[stack[i - k - 1]] == dep[u]; ++k) {
        ls[k] = stack[i - k - 1];
        rs[k] = u;
        dep[n + k] = dep[u] - 1;
        u = n + k;
      }
      stack[i - k] = u;
    }
  }

  // min skew heap
  struct Heap {
    Heap *l, *r;
    T val;
    int id;
    Heap() : l(nullptr), r(nullptr), val(0), id(0) {}
  };
  Heap *meld(Heap *a, Heap *b) {
    if (!a) return b;
    if (!b) return a;
    if (a->val > b->val) swap(a, b);
    a->r = meld(a->r, b);
    swap(a->l, a->r);
    return a;
  }
  void pop(Heap *&a) {
    a = meld(a->l, a->r);
  }
  T secondMin(const Heap *a) {
    return a->l ? (a->r ? min(a->l->val, a->r->val) : a->l->val) : (a->r ? a->r->val : inf);
  }
};
////////////////////////////////////////////////////////////////////////////////

#endif  // LIBRA_OTHER_MIN_BST_H_
