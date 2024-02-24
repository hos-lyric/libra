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

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <random>

using std::cerr;
using std::endl;
using std::mt19937_64;

void unittest() {
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
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupo_predecessor_problem();
  return 0;
}
