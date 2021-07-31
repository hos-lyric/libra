#include <assert.h>
#include <stdio.h>
#include <vector>

using std::vector;

// [0, n), 1 <= n <= 2^(6D)
template <int D> struct Set {
  int n;
  vector<unsigned long long> a[D];
  Set() {}
  Set(int n_) : n(n_) {
    static_assert(1 <= D && D <= 6, "Set: 1 <= D <= 6 must hold");
    assert(1 <= n_ && n_ <= 1LL << (6 * D));
    for (int d = 0; d < D; ++d) {
      n_ = (n_ + 63) >> 6;
      a[d].assign(n_, 0);
    }
  }
  bool empty() const {
    return !a[D - 1][0];
  }
  bool contains(int x) const {
    return (a[0][x >> 6] >> (x & 63)) & 1;
  }
  void insert(int x) {
    for (int d = 0; d < D; ++d) {
      const int q = x >> 6, r = x & 63;
      a[d][q] |= 1ULL << r;
      x = q;
    }
  }
  void erase(int x) {
    for (int d = 0; d < D; ++d) {
      const int q = x >> 6, r = x & 63;
      if ((a[d][q] &= ~(1ULL << r))) break;
      x = q;
    }
  }
  // min s.t. >= x
  int next(int x) const {
    for (int d = 0; d < D; ++d) {
      const int q = x >> 6, r = x & 63;
      if (static_cast<size_t>(q) >= a[d].size()) break;
      const unsigned long long upper = a[d][q] >> r;
      if (upper) {
        x += __builtin_ctzll(upper);
        for (int e = d - 1; e >= 0; --e) x = x << 6 | __builtin_ctzll(a[e][x]);
        return x;
      }
      x = q + 1;
    }
    return n;
  }
  // max s.t. <= x
  int prev(int x) const {
    for (int d = 0; d < D; ++d) {
      if (x < 0) break;
      const int q = x >> 6, r = x & 63;
      const unsigned long long lower = a[d][q] << (63 - r);
      if (lower) {
        x -= __builtin_clzll(lower);
        for (int e = d - 1; e >= 0; --e) x = x << 6 | (63 - __builtin_clzll(a[e][x]));
        return x;
      }
      x = q - 1;
    }
    return -1;
  }
};

void unittest() {
  Set<5> s(123456789);
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
  assert(s.next(400000) == 462743);
  assert(s.next(462743) == 462743);
  assert(s.next(462744) == 793238);
  assert(s.next(800000) == 123456789);
  assert(s.next(123456788) == 123456789);
  assert(s.prev(800000) == 794238);
  assert(s.prev(383289) == 383289);
  assert(s.prev(383288) == 383279);
  assert(s.prev(300000) == -1);
  assert(s.prev(0) == -1);
}


// https://judge.yosupo.jp/problem/predecessor_problem
char T[10000010];

int main() {
  // unittest();
  
  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    scanf("%s", T);
    Set<4> s(N);
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
  return 0;
}
