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

#include <stdio.h>
#include <iostream>

using std::cerr;
using std::endl;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

template <class T>
void checkTree(const vector<T> &as, const MinBST<T, true> &bst) {
  const int n = bst.n;
  assert(static_cast<int>(bst.ls.size()) == n - 1);
  assert(static_cast<int>(bst.rs.size()) == n - 1);
  assert(static_cast<int>(bst.dep.size()) == 2 * n - 1);
  vector<int> par(2 * n - 1, -1);
  // [is[u], js[u]) merged
  vector<int> is(2 * n - 1), js(2 * n - 1);
  vector<T> sums(2 * n - 1);
  for (int i = 0; i < n; ++i) {
    is[i] = i;
    js[i] = i + 1;
    sums[i] = as[i];
  }
  for (int k = 0; k < n - 1; ++k) {
    const int l = bst.ls[k], r = bst.rs[k];
    assert(0 <= l); assert(l < n + k);
    assert(0 <= r); assert(r < n + k);
    assert(js[l] == is[r]);
    assert(bst.dep[n + k] == bst.dep[l] - 1);
    assert(bst.dep[n + k] == bst.dep[r] - 1);
    par[l] = par[r] = n + k;
    is[n + k] = is[l];
    js[n + k] = js[r];
    sums[n + k] = sums[l] + sums[r];
  }
  assert(bst.dep[2 * n - 2] == 0);
  T total = 0;
  for (int i = 0; i < n; ++i) total += as[i] * bst.dep[i];
  assert(bst.total == total);
  for (int u = n; u < 2 * n - 2; ++u) if (~par[u] && ~par[par[u]]) {
    assert(sums[par[par[u]]] >= 2 * sums[u]);
  }
}

void unittest() {
  {
    const vector<int> as{100};
    assert((MinBST<int, /*RECOVER=*/false>(as)).total == 0);
    const MinBST<int, /*RECOVER=*/true> bst(as);
    assert(bst.total == 0);
    assert(bst.ls == (vector<int>{}));
    assert(bst.rs == (vector<int>{}));
    assert(bst.dep == (vector<int>{0}));
  }
  {
    // https://math.mit.edu/~shor/PAM/hu-tucker_algorithm.html
    const vector<int> as{1, 2, 23, 4, 3, 3, 5, 19};
    assert((MinBST<int, /*RECOVER=*/false>(as)).total == 153);
    const MinBST<int, /*RECOVER=*/true> bst(as);
    assert(bst.total == 153);
    assert(bst.ls == (vector<int>{0, 8, 3, 5, 10, 12, 9}));
    assert(bst.rs == (vector<int>{1, 2, 4, 6, 11, 7, 13}));
    assert(bst.dep == (vector<int>{3, 3, 2, 4, 4, 4, 4, 2, 2, 1, 3, 3, 2, 1, 0}));
    checkTree(as, bst);
  }
  {
    // can fail if tie-breaking is inconsistent
    const vector<int> as{
        10, 10, 12, 4, 16, 13, 6, 20, 19, 14, 13, 17, 16, 20, 11, 20, 3, 5};
    assert((MinBST<int, /*RECOVER=*/false>(as)).total == 940);
    const MinBST<int, /*RECOVER=*/true> bst(as);
    assert(bst.total == 940);
    checkTree(as, bst);
  }
  {
    constexpr int NUM_CASES = 100'000;
    constexpr long long INF = 1'000'000'000'000'000'000LL;
    for (const int maxN : {10, 30, 100}) {
      for (const int maxA : {10, 30, 100, 1'000'000'000}) {
        for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
          const int n = 1 + xrand() % maxN;
          vector<long long> as(n);
          for (int i = 0; i < n; ++i) as[i] = xrand() % (maxA + 1);
          vector<long long> asSum(n + 1);
          asSum[0] = 0;
          for (int i = 0; i < n; ++i) asSum[i + 1] = asSum[i] + as[i];
          vector<vector<long long>> dp(n + 1, vector<long long>(n + 1, INF));
          for (int i = 0; i < n; ++i) dp[i][i + 1] = 0;
          for (int i = n; --i >= 0; ) for (int j = i + 2; j <= n; ++j) {
            for (int k = i + 1; k < j; ++k) {
              if (dp[i][j] > dp[i][k] + dp[k][j]) {
                dp[i][j] = dp[i][k] + dp[k][j];
              }
            }
            dp[i][j] += (asSum[j] - asSum[i]);
          }
          assert((MinBST<long long, /*RECOVER=*/false>(as)).total == dp[0][n]);
          const MinBST<long long, /*RECOVER=*/true> bst(as);
          assert(bst.total == dp[0][n]);
          checkTree(as, bst);
        }
      }
    }
  }
}

// https://atcoder.jp/contests/atc002/tasks/atc002_c
void solve_int() {
  int N;
  for (; ~scanf("%d", &N); ) {
    vector<int> A(N);
    for (int i = 0; i < N; ++i) scanf("%d", &A[i]);
    const MinBST<int, /*RECOVER=*/false> bst(A);
    printf("%d\n", bst.total);
  }
}
void solve_long() {
  int N;
  for (; ~scanf("%d", &N); ) {
    vector<long long> A(N);
    for (int i = 0; i < N; ++i) scanf("%lld", &A[i]);
    const MinBST<long long, /*RECOVER=*/false> bst(A);
    printf("%lld\n", bst.total);
  }
}
void solve_recover_int() {
  int N;
  for (; ~scanf("%d", &N); ) {
    vector<int> A(N);
    for (int i = 0; i < N; ++i) scanf("%d", &A[i]);
    const MinBST<int, /*RECOVER=*/true> bst(A);
    checkTree(A, bst);
    printf("%d\n", bst.total);
  }
}
void solve_recover_long() {
  int N;
  for (; ~scanf("%d", &N); ) {
    vector<long long> A(N);
    for (int i = 0; i < N; ++i) scanf("%lld", &A[i]);
    const MinBST<long long, /*RECOVER=*/true> bst(A);
    checkTree(A, bst);
    printf("%lld\n", bst.total);
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // solve_int();
  // solve_long();
  // solve_recover_int();
  // solve_recover_long();
  return 0;
}
