#include <assert.h>
#include <utility>
#include <vector>

using std::pair;
using std::vector;

template <class T> struct DisjointSparseTable {
  int logN, n;
  vector<T> ts;
  DisjointSparseTable() {}
  template <class S> explicit DisjointSparseTable(const vector<S> &ss) {
    n = ss.size();
    for (logN = 1; 1 << logN < n; ++logN) {}
    ts.resize(logN * n);
    for (int i = 0; i < n; ++i) ts[i] = T(ss[i]);
    for (int h = 1; h < logN; ++h) {
      T *ths = ts.data() + h * n;
      for (int i = 1 << h; i < n; i += 1 << (h + 1)) {
        ths[i - 1] = ts[i - 1];
        for (int j = i - 1; --j >= i - (1 << h); ) ths[j] = ths[j + 1].mulLeft(ss[j]);
        ths[i] = ts[i];
        for (int j = i + 1; j < i + (1 << h) && j < n; ++j) ths[j] = ths[j - 1].mulRight(ss[j]);
      }
    }
  }
  pair<T, T> getPair(int a, int b) const {
    assert(0 <= a); assert(a <= b); assert(b <= n);
    if (a == b) return std::make_pair(T(), T());
    if (a + 1 == b) return std::make_pair(T(), ts[a]);
    const int h = 31 - __builtin_clz(a ^ (b - 1));
    return std::make_pair(ts[h * n + a], ts[h * n + (b - 1)]);
  }
  T get(int a, int b) const {
    const auto res = getPair(a, b);
    return res.first * res.second;
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>

using std::cerr;
using std::endl;

struct Node {
  int a, b;
  Node() : a(0), b(0) {}
  Node(int a_, int b_) : a(a_), b(b_) {}
  explicit Node(int i) : a(i), b(i + 1) {}
  friend Node operator*(const Node &l, const Node &r) {
    if (l.a == l.b) return r;
    if (r.a == r.b) return l;
    assert(l.b == r.a);
    return Node(l.a, r.b);
  }
  Node mulLeft(int i) const {
    assert(i == a - 1);
    return Node(a - 1, b);
  }
  Node mulRight(int i) const {
    assert(i == b);
    return Node(a, b + 1);
  }
};

void unittest() {
  {
    /*
      0 1 2 3 4 5 6 7 8 9 10
      -|- -|- -|- -|- -|- -|
      ---|--- ---|--- ---|
        -|-     -|-     -|-
      -------|-------
        -----|-----
          ---|---
            -|-
      ---------------|
        -------------|
          -----------|
            ---------|
              -------|
                -----|-----
                  ---|---
                    -|-
    */
    const int n = 11;
    vector<int> ss(n);
    for (int i = 0; i < n; ++i) ss[i] = i;
    const DisjointSparseTable<Node> dst(ss);
    auto check = [&](int h, int i, int a, int b) -> void {
      assert(dst.ts[h * n + i].a == a);
      assert(dst.ts[h * n + i].b == b);
    };
    check(0, 0, 0, 1);
    check(0, 1, 1, 2);
    check(0, 2, 2, 3);
    check(0, 3, 3, 4);
    check(0, 4, 4, 5);
    check(0, 5, 5, 6);
    check(0, 6, 6, 7);
    check(0, 7, 7, 8);
    check(0, 8, 8, 9);
    check(0, 9, 9, 10);
    check(0, 10, 10, 11);
    check(1, 0, 0, 2);
    check(1, 1, 1, 2);
    check(1, 2, 2, 3);
    check(1, 3, 2, 4);
    check(1, 4, 4, 6);
    check(1, 5, 5, 6);
    check(1, 6, 6, 7);
    check(1, 7, 6, 8);
    check(1, 8, 8, 10);
    check(1, 9, 9, 10);
    check(1, 10, 10, 11);
    check(2, 0, 0, 4);
    check(2, 1, 1, 4);
    check(2, 2, 2, 4);
    check(2, 3, 3, 4);
    check(2, 4, 4, 5);
    check(2, 5, 4, 6);
    check(2, 6, 4, 7);
    check(2, 7, 4, 8);
    check(3, 0, 0, 8);
    check(3, 1, 1, 8);
    check(3, 2, 2, 8);
    check(3, 3, 3, 8);
    check(3, 4, 4, 8);
    check(3, 5, 5, 8);
    check(3, 6, 6, 8);
    check(3, 7, 7, 8);
    check(3, 8, 8, 9);
    check(3, 9, 8, 10);
    check(3, 10, 8, 11);
  }
  for (int n = 0; n <= 100; ++n) {
    vector<int> ss(n);
    for (int i = 0; i < n; ++i) ss[i] = i;
    const DisjointSparseTable<Node> dst(ss);
    for (int a = 0; a <= n; ++a) for (int b = a; b <= n; ++b) {
      const Node res = dst.get(a, b);
      if (a == b) {
        assert(res.a == 0);
        assert(res.b == 0);
      } else {
        assert(res.a == a);
        assert(res.b == b);
      }
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
