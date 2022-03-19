#include <assert.h>
#include <vector>

using std::vector;

// root: min (tie-break: left)
struct MinCartesianTree {
  int n, rt;
  vector<int> par, lef, rig;
  template <class T> void build(int n_, T *as) {
    assert(n_ >= 1);
    n = n_;
    rt = 0;
    par.assign(n, -1);
    lef.assign(n, -1);
    rig.assign(n, -1);
    int top = 0;
    vector<int> stack(n, 0);
    for (int u = 1; u < n; ++u) {
      if (as[stack[top]] > as[u]) {  // >
        for (; top >= 1 && as[stack[top - 1]] > as[u]; --top) {}  // >
        if (top == 0) {
          rt = par[lef[u] = stack[top]] = u;
        } else {
          par[lef[u] = stack[top]] = u;
          rig[par[u] = stack[top - 1]] = u;
        }
        stack[top] = u;
      } else {
        rig[par[u] = stack[top]] = u;
        stack[++top] = u;
      }
    }
  }
  template <class T> void build(const T &as) {
    build(as.size(), as.data());
  }
};

// root: max (tie-break: left)
struct MaxCartesianTree {
  int n, rt;
  vector<int> par, lef, rig;
  template <class T> void build(int n_, T *as) {
    assert(n_ >= 1);
    n = n_;
    rt = 0;
    par.assign(n, -1);
    lef.assign(n, -1);
    rig.assign(n, -1);
    int top = 0;
    vector<int> stack(n, 0);
    for (int u = 1; u < n; ++u) {
      if (as[stack[top]] < as[u]) {  // <
        for (; top >= 1 && as[stack[top - 1]] < as[u]; --top) {}  // <
        if (top == 0) {
          rt = par[lef[u] = stack[top]] = u;
        } else {
          par[lef[u] = stack[top]] = u;
          rig[par[u] = stack[top - 1]] = u;
        }
        stack[top] = u;
      } else {
        rig[par[u] = stack[top]] = u;
        stack[++top] = u;
      }
    }
  }
  template <class T> void build(const T &as) {
    build(as.size(), as.data());
  }
};

////////////////////////////////////////////////////////////////////////////////

void unittestMin() {
  auto check = [&](const vector<int> &as, const MinCartesianTree &ct) -> void {
    assert(0 <= ct.rt); assert(ct.rt < ct.n);
    assert(ct.par.size() == static_cast<size_t>(ct.n));
    assert(ct.lef.size() == static_cast<size_t>(ct.n));
    assert(ct.rig.size() == static_cast<size_t>(ct.n));
    assert(ct.par[ct.rt] == -1);
    for (int u = 0; u < ct.n; ++u) {
      if (u != ct.rt) {
        const int p = ct.par[u];
        assert(0 <= p); assert(p < ct.n);
        assert(ct.lef[p] == u || ct.rig[p] == u);
      }
      const int l = ct.lef[u];
      if (l != -1) {
        assert(0 <= l); assert(l < u);
        assert(u == ct.par[l]);
        assert(as[l] > as[u]);
      }
      const int r = ct.rig[u];
      if (r != -1) {
        assert(u < r); assert(r < ct.n);
        assert(u == ct.par[r]);
        assert(as[u] <= as[r]);
      }
    }
  };
  {
    const long long as[7] = {3, 1, 4, 1, 5, 9, 2};
    MinCartesianTree ct;
    ct.build(7, as);
    assert(ct.n == 7);
    assert(ct.rt == 1);
    assert(ct.par == (vector<int>{1, -1, 3, 1, 6, 4, 3}));
    assert(ct.lef == (vector<int>{-1, 0, -1, 2, -1, -1, 4}));
    assert(ct.rig == (vector<int>{-1, 3, -1, 6, 5, -1, -1}));
    check({3, 1, 4, 1, 5, 9, 2}, ct);
  }
  
  auto test = [&](const vector<int> &as) {
    MinCartesianTree ct;
    ct.build(as);
    check(as, ct);
  };
#define rep(a, m) for (int a = 0; a < m; ++a)
  rep(a0, 1) test({a0});
  rep(a0, 2) rep(a1, 2) test({a0, a1});
  rep(a0, 3) rep(a1, 3) rep(a2, 3) test({a0, a1, a2});
  rep(a0, 4) rep(a1, 4) rep(a2, 4) rep(a3, 4) test({a0, a1, a2, a3});
  rep(a0, 5) rep(a1, 5) rep(a2, 5) rep(a3, 5) rep(a4, 5) test({a0, a1, a2, a3, a4});
  rep(a0, 6) rep(a1, 6) rep(a2, 6) rep(a3, 6) rep(a4, 6) rep(a5, 6) test({a0, a1, a2, a3, a4, a5});
#undef rep
}

void unittestMax() {
  auto check = [&](const vector<int> &as, const MaxCartesianTree &ct) -> void {
    assert(0 <= ct.rt); assert(ct.rt < ct.n);
    assert(ct.par.size() == static_cast<size_t>(ct.n));
    assert(ct.lef.size() == static_cast<size_t>(ct.n));
    assert(ct.rig.size() == static_cast<size_t>(ct.n));
    assert(ct.par[ct.rt] == -1);
    for (int u = 0; u < ct.n; ++u) {
      if (u != ct.rt) {
        const int p = ct.par[u];
        assert(0 <= p); assert(p < ct.n);
        assert(ct.lef[p] == u || ct.rig[p] == u);
      }
      const int l = ct.lef[u];
      if (l != -1) {
        assert(0 <= l); assert(l < u);
        assert(u == ct.par[l]);
        assert(as[l] < as[u]);
      }
      const int r = ct.rig[u];
      if (r != -1) {
        assert(u < r); assert(r < ct.n);
        assert(u == ct.par[r]);
        assert(as[u] >= as[r]);
      }
    }
  };
  {
    const long long as[7] = {3, 1, 4, 1, 5, 9, 2};
    MaxCartesianTree ct;
    ct.build(7, as);
    assert(ct.n == 7);
    assert(ct.rt == 5);
    assert(ct.par == (vector<int>{2, 0, 4, 2, 5, -1, 5}));
    assert(ct.lef == (vector<int>{-1, -1, 0, -1, 2, 4, -1}));
    assert(ct.rig == (vector<int>{1, -1, 3, -1, -1, 6, -1}));
    check({3, 1, 4, 1, 5, 9, 2}, ct);
  }
  
  auto test = [&](const vector<int> &as) {
    MaxCartesianTree ct;
    ct.build(as);
    check(as, ct);
  };
#define rep(a, m) for (int a = 0; a < m; ++a)
  rep(a0, 1) test({a0});
  rep(a0, 2) rep(a1, 2) test({a0, a1});
  rep(a0, 3) rep(a1, 3) rep(a2, 3) test({a0, a1, a2});
  rep(a0, 4) rep(a1, 4) rep(a2, 4) rep(a3, 4) test({a0, a1, a2, a3});
  rep(a0, 5) rep(a1, 5) rep(a2, 5) rep(a3, 5) rep(a4, 5) test({a0, a1, a2, a3, a4});
  rep(a0, 6) rep(a1, 6) rep(a2, 6) rep(a3, 6) rep(a4, 6) rep(a5, 6) test({a0, a1, a2, a3, a4, a5});
#undef rep
}

// https://judge.yosupo.jp/problem/cartesian_tree
#include <stdio.h>
void yosupoMin_cartesian_tree() {
  int N;
  for (; ~scanf("%d", &N); ) {
    vector<int> A(N);
    for (int u = 0; u < N; ++u) {
      scanf("%d", &A[u]);
    }
    MinCartesianTree ct;
    ct.build(A);
    for (int u = 0; u < N; ++u) {
      if (u) printf(" ");
      printf("%d", (u == ct.rt) ? u : ct.par[u]);
    }
    puts("");
  }
}
void yosupoMax_cartesian_tree() {
  int N;
  for (; ~scanf("%d", &N); ) {
    vector<int> A(N);
    for (int u = 0; u < N; ++u) {
      scanf("%d", &A[u]);
      A[u] *= -1;
    }
    MaxCartesianTree ct;
    ct.build(A);
    for (int u = 0; u < N; ++u) {
      if (u) printf(" ");
      printf("%d", (u == ct.rt) ? u : ct.par[u]);
    }
    puts("");
  }
}

int main() {
  unittestMin();
  unittestMax();
  // yosupoMin_cartesian_tree();
  // yosupoMax_cartesian_tree();
  return 0;
}
