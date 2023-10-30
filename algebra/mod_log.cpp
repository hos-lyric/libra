#include <algorithm>
#include <utility>
#include "modint.h"

using std::pair;

// M = 2^K N + 1
// init: O(2^(K/2) + N), query: O(log(M))
// g must be a primitive root
template <unsigned M_> struct ModLog {
  static constexpr unsigned M = M_;
  static constexpr int K = __builtin_ctz(M - 1);
  static constexpr int N = (M - 1) >> K;
  static_assert(M == (N << K) + 1, "[ModLog] M = 2^K N + 1 must hold.");
  const ModInt<M> g;
  // N^-1 mod 2^K
  unsigned invN;
  // (g^N)^(-2^*)
  ModInt<M> hs[K];
  // ((g^N)^(2^floor(K/2)))^*, (g^(2^K))^*
  pair<unsigned, int> ps[1 << (K-K/2)], qs[N];
  ModLog() {}
  explicit ModLog(ModInt<M> g_) : g(g_) {
    invN = N;
    for (int i = 0; i < 4; ++i) invN *= (2 - N * invN);
    invN &= ((1 << K) - 1);
    hs[0] = g.pow(-N);
    for (int k = 1; k < K; ++k) hs[k] = hs[k - 1] * hs[k - 1];
    const ModInt<M> p = g.pow(N << (K/2));
    ModInt<M> pp = 1;
    for (int x = 0; x < 1 << (K-K/2); ++x) { ps[x] = std::make_pair(pp.x, x); pp *= p; }
    std::sort(ps, ps + (1 << (K-K/2)));
    const ModInt<M> q = g.pow(1 << K);
    ModInt<M> qq = 1;
    for (int y = 0; y < N; ++y) { qs[y] = std::make_pair(qq.x, y); qq *= q; }
    std::sort(qs, qs + N);
  }
  int operator()(ModInt<M> a) const {
    assert(a);
    // mod 2^K
    ModInt<M> b = a.pow(N);
    ModInt<M> bb = b;
    for (int k = 0; k < K/2; ++k) bb *= bb;
    int x = std::partition_point(ps, ps + (1 << (K-K/2)), [&](const pair<unsigned, int> &p) -> bool {
      return (p.first < bb.x);
    })->second;
    for (int k = 0; k < K-K/2; ++k) if (x >> k & 1) b *= hs[k];
    x |= (std::partition_point(ps, ps + (1 << (K-K/2)), [&](const pair<unsigned, int> &p) -> bool {
      return (p.first < b.x);
    })->second) << (K/2);
    // mod N
    ModInt<M> c = a;
    for (int k = 0; k < K; ++k) c *= c;
    const int y = std::partition_point(qs, qs + N, [&](const pair<unsigned, int> &q) -> bool {
      return (q.first < c.x);
    })->second;
    return y + N * static_cast<int>((static_cast<long long>(invN) * (x - y)) & ((1 << K) - 1));
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <vector>

using std::cerr;
using std::endl;
using std::vector;

// [0, 2^32)
unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

template <int MO> void testAll() {
  for (int i = 1; i < MO; ++i) {
    const ModInt<MO> g = i;
    bool isPrimitiveRoot = true;
    ModInt<MO> gg = 1;
    for (int e = 0; e < MO - 1; ++e) {
      isPrimitiveRoot = isPrimitiveRoot && (e == 0 || gg != 1);
      gg *= g;
    }
    assert(gg == 1);
    if (isPrimitiveRoot) {
      ModLog<MO> l(g);
      cerr << "[testAll] MO = " << MO << " = 2^" << l.K << " " << l.N << " + 1, "
           << "g = " << g << endl;
      for (int e = 0; e < MO - 1; ++e) {
        assert(l(gg) == e);
        gg *= g;
      }
    }
  }
}

void unittest() {
  {
    constexpr int MO = 998244353;
    constexpr ModInt<MO> g = 3;
    ModLog<MO> l(3);
    for (int e = 0; e < 100; ++e) {
      const ModInt<MO> a = g.pow(e);
      assert(l(a) == e);
    }
    for (int i = 1; i < 100; ++i) {
      const ModInt<MO> a = i;
      const int e = l(a);
      assert(0 <= e); assert(e < MO - 1);
      assert(g.pow(e) == a);
    }
    for (int i = 1; i < 100; ++i) {
      const ModInt<MO> a = MO - i;
      const int e = l(a);
      assert(0 <= e); assert(e < MO - 1);
      assert(g.pow(e) == a);
    }
  }
  testAll<3>();
  testAll<5>();
  testAll<7>();
  testAll<11>();
  testAll<13>();
  testAll<17>();
  testAll<19>();
  testAll<23>();
  testAll<29>();
  testAll<31>();
  testAll<37>();
  testAll<41>();
  testAll<43>();
  testAll<47>();
  testAll<53>();
  testAll<59>();
  testAll<61>();
  testAll<67>();
  testAll<71>();
  testAll<73>();
  testAll<79>();
  testAll<83>();
  testAll<89>();
  testAll<97>();
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
