#include <assert.h>
#include <vector>

using std::vector;

struct Set {
  // max{ceil(log_64(n)), 1}
  int log64N, n;
  vector<unsigned long long> a[6];
  explicit Set(int n_ = 0) : n(n_) {
    assert(n >= 0);
    int m = n ? n : 1;
    for (int d = 0; ; ++d) {
      m = (m + 63) >> 6;
      a[d].assign(m, 0);
      if (m == 1) {
        log64N = d + 1;
        break;
      }
    }
  }
  bool empty() const {
    return !a[log64N - 1][0];
  }
  bool contains(int x) const {
    return (a[0][x >> 6] >> (x & 63)) & 1;
  }
  void insert(int x) {
    for (int d = 0; d < log64N; ++d) {
      const int q = x >> 6, r = x & 63;
      a[d][q] |= 1ULL << r;
      x = q;
    }
  }
  void erase(int x) {
    for (int d = 0; d < log64N; ++d) {
      const int q = x >> 6, r = x & 63;
      if ((a[d][q] &= ~(1ULL << r))) break;
      x = q;
    }
  }
  // max s.t. <= x (or -1)
  int prev(int x) const {
    if (x > n - 1) x = n - 1;
    for (int d = 0; d <= log64N; ++d) {
      if (x < 0) break;
      const int q = x >> 6, r = x & 63;
      const unsigned long long lower = a[d][q] << (63 - r);
      if (lower) {
        x -= __builtin_clzll(lower);
        for (int e = d; --e >= 0; ) x = x << 6 | (63 - __builtin_clzll(a[e][x]));
        return x;
      }
      x = q - 1;
    }
    return -1;
  }
  // min s.t. >= x (or n)
  int next(int x) const {
    if (x < 0) x = 0;
    for (int d = 0; d < log64N; ++d) {
      const int q = x >> 6, r = x & 63;
      if (static_cast<unsigned>(q) >= a[d].size()) break;
      const unsigned long long upper = a[d][q] >> r;
      if (upper) {
        x += __builtin_ctzll(upper);
        for (int e = d; --e >= 0; ) x = x << 6 | __builtin_ctzll(a[e][x]);
        return x;
      }
      x = q + 1;
    }
    return n;
  }
};

template <class T> struct Painter {
  int n;
  Set s;
  vector<T> ts;
  Painter() {}
  Painter(int n_, const T &t) : n(n_), s(n + 1), ts(n + 2, t) {}
  template <class F> void paint(int a, int b, const T &t, F f) {
    assert(0 <= a); assert(a <= b); assert(b <= n);
    if (a == b) return;
    // auto it = this->lower_bound(a);
    int c = s.next(a);
    if (b < c) {
      f(a, b, ts[c]);
      s.insert(a); ts[a] = ts[c];
      s.insert(b); ts[b] = t;
    } else if (a < c) {
      const T ta = ts[c];
      int k = a;
      for (; c <= b; s.erase(c), c = s.next(c)) {
        f(k, c, ts[c]);
        k = c;
      }
      if (k < b) {
        f(k, b, ts[c]);
      }
      s.insert(a); ts[a] = ta;
      s.insert(b); ts[b] = t;
    } else {
      c = s.next(c + 1);
      int k = a;
      for (; c <= b; s.erase(c), c = s.next(c)) {
        f(k, c, ts[c]);
        k = c;
      }
      if (k < b) {
        f(k, b, ts[c]);
      }
      s.insert(b); ts[b] = t;
    }
  }
  void paint(int a, int b, const T &t) {
    paint(a, b, t, [&](int, int, const T &) -> void {});
  }
  T get(int k) const {
    assert(0 <= k); assert(k < n);
    return ts[s.next(k + 1)];
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <random>
#include <string>

using std::cerr;
using std::endl;
using std::mt19937_64;
using std::string;

void unittest_Set() {
  {
    Set s;
    assert(s.empty());
    assert(s.prev(-1) == -1);
    assert(s.prev(0) == -1);
    assert(s.prev(1) == -1);
    assert(s.next(-1) == 0);
    assert(s.next(0) == 0);
    assert(s.next(1) == 0);
  }
  {
    Set s(1);
    assert(s.empty());
    assert(!s.contains(0));
    assert(s.prev(-1) == -1);
    assert(s.prev(0) == -1);
    assert(s.prev(1) == -1);
    assert(s.next(-1) == 1);
    assert(s.next(0) == 1);
    assert(s.next(1) == 1);
    s.insert(0);
    assert(!s.empty());
    assert(s.contains(0));
    assert(s.prev(-1) == -1);
    assert(s.prev(0) == 0);
    assert(s.prev(1) == 0);
    assert(s.next(-1) == 0);
    assert(s.next(0) == 0);
    assert(s.next(1) == 1);
    s.erase(0);
    assert(s.empty());
    assert(!s.contains(0));
    assert(s.prev(-1) == -1);
    assert(s.prev(0) == -1);
    assert(s.prev(1) == -1);
    assert(s.next(-1) == 1);
    assert(s.next(0) == 1);
    assert(s.next(1) == 1);
  }
  {
    Set s(123456789);
    assert(s.empty());
    s.insert(314159);
    s.insert(141592);
    assert(!s.empty());
    s.erase(314159);
    s.erase(141592);
    assert(s.empty());
    s.insert(653589);
    s.insert(793238);
    s.insert(462643);
    s.erase(653589);
    s.insert(383279);
    s.insert(502884);
    s.erase(502884);
    s.insert(383289);
    s.insert(462743);
    s.insert(794238);
    s.erase(462643);
    // {383279, 383289, 462743, 793238, 794238}
    assert(s.prev(1001001001) == 794238);
    assert(s.prev(800000) == 794238);
    assert(s.prev(383289) == 383289);
    assert(s.prev(383288) == 383279);
    assert(s.prev(300000) == -1);
    assert(s.prev(0) == -1);
    assert(s.prev(-1001001001) == -1);
    assert(s.next(-1001001001) == 383279);
    assert(s.next(400000) == 462743);
    assert(s.next(462743) == 462743);
    assert(s.next(462744) == 793238);
    assert(s.next(800000) == 123456789);
    assert(s.next(123456788) == 123456789);
    assert(s.next(1001001001) == 123456789);
  }
  {
    mt19937_64 rng;
    for (const int n : {2, 63, 64, 65, 64 * 64 - 1, 64 * 64, 64 * 64 + 1}) {
      vector<int> on(n, 0);
      Set s(n);
      for (int q = 0; q < 1000; ++q) {
        {
          const int x = rng() % n;
          if (on[x]) {
            on[x] = 0;
            s.erase(x);
          } else {
            on[x] = 1;
            s.insert(x);
          }
        }
        {
          const int x = rng() % n;
          int l, r;
          for (l = x; l >= 0 && !on[l]; --l) {}
          for (r = x; r < n && !on[r]; ++r) {}
          assert(s.prev(x) == l);
          assert(s.next(x) == r);
        }
      }
    }
  }
}

void unittest_Painter() {
  {
    Painter<string> painter(9, "-1");
    painter.paint(0, 5, "-2");
    painter.paint(3, 6, "-3");
    painter.paint(4, 8, "-4");
    painter.paint(2, 7, "-5");
    painter.paint(5, 9, "-6");
    painter.paint(2, 7, "-7");
    painter.paint(5, 9, "-8");
    painter.paint(1, 5, "-9");
    assert(painter.get(0) == "-2");
    assert(painter.get(1) == "-9");
    assert(painter.get(2) == "-9");
    assert(painter.get(3) == "-9");
    assert(painter.get(4) == "-9");
    assert(painter.get(5) == "-8");
    assert(painter.get(6) == "-8");
    assert(painter.get(7) == "-8");
    assert(painter.get(8) == "-8");
  }
  mt19937_64 rng;
  for (int caseId = 0; caseId < 1000; ++caseId) {
    const int n = 1 + rng() % 1000;
    vector<int> brt(n, -1), sol(n, -1);
    Painter<int> painter(n, -1);
    for (int queryId = 0; queryId < 1000; ++queryId) {
      for (; ; ) {
        const int a = rng() % (n + 1);
        const int b = rng() % (n + 1);
        if (a <= b) {
          for (int i = a; i < b; ++i) {
            brt[i] = queryId;
          }
          painter.paint(a, b, queryId, [&](int l, int r, int old) -> void {
            assert(0 <= l); assert(l < r); assert(r <= n);
            for (int i = l; i < r; ++i) {
              assert(sol[i] == old);
              sol[i] = queryId;
            }
          });
          for (int i = 0; i < n; ++i) {
            assert(sol[i] == painter.get(i));
          }
          assert(brt == sol);
          break;
        }
      }
    }
  }
}

// https://judge.yosupo.jp/problem/predecessor_problem
#include <stdio.h>
char T[10'000'010];
void yosupo_predecessor_problem() {
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    scanf("%s", T);
    Set s(N);
    for (int i = 0; i < N; ++i) {
      if (T[i] == '1') {
        s.insert(i);
      }
    }
    for (; Q--; ) {
      int typ, k;
      scanf("%d%d", &typ, &k);
      switch (typ) {
        case 0: {
          s.insert(k);
        } break;
        case 1: {
          s.erase(k);
        } break;
        case 2: {
          const bool ans = s.contains(k);
          puts(ans ? "1" : "0");
        } break;
        case 3: {
          const int ans = s.next(k);
          printf("%d\n", (ans >= N) ? -1 : ans);
        } break;
        case 4: {
          const int ans = s.prev(k);
          printf("%d\n", ans);
        } break;
        default: assert(false);
      }
    }
  }
}

int main() {
  unittest_Set(); cerr << "PASSED unittest_Set" << endl;
  unittest_Painter(); cerr << "PASSED unittest_Painter" << endl;
  // yosupo_predecessor_problem();
  return 0;
}
