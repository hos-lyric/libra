#include <vector>

using std::vector;

template <class T, class Op> struct SegmentTree {
  const Op op;
  const T idT;

  int n;
  vector<T> ts;
  SegmentTree(int n_, const Op op, const T &idT) : op(op), idT(idT) {
    for (n = 1; n < n_; n <<= 1) {}
    ts.assign(n << 1, idT);
  }
  SegmentTree(const vector<T> &ts_, const Op op, const T &idT)
      : op(op), idT(idT) {
    const int n_ = ts_.size();
    for (n = 1; n < n_; n <<= 1) {}
    ts.assign(n << 1, idT);
    for (int a = 0; a < n_; ++a) ts[n + a] = ts_[a];
    build();
  }
  T &at(int a) {
    return ts[n + a];
  }
  void build() {
    for (int a = n; --a; ) ts[a] = op(ts[a << 1], ts[a << 1 | 1]);
  }
  void set(int a, const T &val) {
    ts[a += n] = val;
    for (; a >>= 1; ) ts[a] = op(ts[a << 1], ts[a << 1 | 1]);
  }
  void mulL(int a, const T &val) {
    set(a, op(val, ts[a + n]));
  }
  void mulR(int a, const T &val) {
    set(a, op(ts[a + n], val));
  }
  T query(int a, int b) const {
    T prodL = idT, prodR = idT;
    for (a += n, b += n; a < b; a >>= 1, b >>= 1) {
      if (a & 1) prodL = op(prodL, ts[a++]);
      if (b & 1) prodR = op(ts[--b], prodR);
    }
    return op(prodL, prodR);
  }

  // min b s.t. pred(prod of [a, b)) (or n + 1 if no such b)
  //   0 <= a <= n
  //   assume pred(prod of [a, b)) is non-decreasing in b
  template <class Pred> int binarySearchR(int a, Pred pred) const {
    if (pred(idT)) return a;
    if (a == n) return n + 1;
    T prod = idT;
    for (a += n; ; a >>= 1) {
      if (a & 1) {
        if (pred(op(prod, ts[a]))) {
          for (; a < n; ) {
            a <<= 1;
            if (!pred(op(prod, ts[a]))) {
              prod = op(prod, ts[a++]);
            }
          }
          return a - n + 1;
        }
        prod = op(prod, ts[a++]);
        if (!(a & (a - 1))) return n + 1;
      }
    }
  }

  // max a s.t. pred(prod of [a, b)) (or -1 if no such a)
  //   0 <= b <= n
  //   assume pred(prod of [a, b)) is non-increasing in a
  template <class Pred> int binarySearchL(int b, Pred pred) const {
    if (pred(idT)) return b;
    if (b == 0) return -1;
    T prod = idT;
    for (b += n; ; b >>= 1) {
      if ((b & 1) || b == 2) {
        if (pred(op(prod, ts[b - 1]))) {
          for (; b <= n; ) {
            b <<= 1;
            if (!pred(op(prod, ts[b - 1]))) {
              prod = op(prod, ts[--b]);
            }
          }
          return b - n - 1;
        }
        prod = op(prod, ts[--b]);
        if (!(b & (b - 1))) return -1;
      }
    }
  }
};

#include <assert.h>
#include <stdio.h>
#include <algorithm>
#include <functional>
#include <string>

using std::max;
using std::min;
using std::string;

void unittest() {
  constexpr int n = 26;
  vector<string> ini(n);
  for (int i = 0; i < n; ++i) {
    ini[i] = string(1, 'a' + i);
  }
  auto op = [](const string &t0, const string &t1) {
    return t0 + t1;
  };
  SegmentTree<string, decltype(op)> seg(ini, op, "");
  seg.set(15, "P");
  seg.mulL(17, "^");
  seg.mulR(19, "$");
  seg.set(21, "V");
  assert(seg.at(17) == "^r");
  assert(seg.query(15, 21) == "Pq^rst$u");
}

// binarySearch
void unittest_binarySearch() {
  constexpr int n = 1 << 4;
  SegmentTree<int, decltype(std::plus<int>())> seg(n, std::plus<int>(), 0);
  for (int i = 0; i < n; ++i) {
    seg.mulR(i, 1);
  }
  for (int i = 0; i <= n; ++i) {
    for (int d = 0; d <= n + 1; ++d) {
      assert(seg.binarySearchR(i, [&d](int s) { return (s >= d); }) ==
             min(i + d, n + 1));
      assert(seg.binarySearchL(i, [&d](int s) { return (s >= d); }) ==
             max(i - d, -1));
    }
  }
}

int main() {
  unittest();
  unittest_binarySearch();
  return 0;
}
