#include "suffix_array.h"

#include <assert.h>
#include <string.h>
#include <utility>
#include <vector>

using std::make_pair;
using std::pair;
using std::vector;

// https://codeforces.com/blog/entry/106725
// Lyndon
//   * smaller than non-trivial suffix
//   * smaller than other cyclic shift
// Lyndon factorization (Lyndon factors in non-incr. order):
//   * longest Lyndon prefix greedily
//   * min suffix greedily (removing min suffix does not change the suffix order)

// pqs[v] = (p, q): Lyndon factorization of as[0, v) ends with a[v - p, v)^q
//   String: string, vector<int>, vector<long long>
//   O(n) time
//
// min_u as[u, v) bs:
//   for (int u = v; ; ) {
//     // candidate u
//     if (v == 0) break;
//     const int p = pqs[u].first, q = pqs[u].second;
//     const int uu = u - q * p;
//     if (!(p >= v - u && sa.lcp(uu, u) >= v - u)) break;
//     // (v - u) is at least doubled
//     u = uu;
//   }
// }
template <class String>
vector<pair<int, int>> lyndonSuffix(const String &as) {
  const int n = as.size();
  vector<pair<int, int>> pqs(n + 1);
  pqs[0] = make_pair(0, 0);
  for (int u = 0; u < n; ) {
    for (int p = 1, q = 1, r = 0, v = u + 1; ; ++v) {
      // as[u, v) = as[u, u + p)^q as[u, u + r)
      // as[u, u + p): Lyndon
      pqs[v] = (r != 0) ? pqs[u + r] : make_pair(p, q);
      if (v == n || as[v - p] > as[v]) {
        u = v - r;
        break;
      } else if (as[v - p] < as[v]) {
        p = v + 1 - u; q = 1; r = 0;
      } else {
        if (++r == p) { ++q; r = 0; }
      }
    }
  }
  return pqs;
}

// as[u, vs[u]): longest Lyndon prefix of as[u, n)
//   String: string, vector<int>, vector<long long>
//   O(n) time
template <class String>
vector<int> lyndonPrefix(const String &as, const SuffixArray &sa) {
  const int n = as.size();
  // top: larger suffix
  int stackLen = 0;
  vector<int> stack(n + 1);
  vector<int> vs(n);
  for (int u = 0; u <= n; ++u) {
    for (; stackLen > 0 && sa.su[stack[stackLen - 1]] > sa.su[u]; --stackLen) {
      vs[stack[stackLen - 1]] = u;
    }
    stack[stackLen++] = u;
  }
  return vs;
}
template <class String>
vector<int> lyndonPrefix(const String &as) {
  return lyndonPrefix(as, SuffixArray(as, /*rmq=*/false));
}

// lyndonPrefix for invert(as), using suffix array of as
template <class String>
vector<int> lyndonPrefixInverted(const String &as, const SuffixArray &sa) {
  assert(sa.rmq);
  const int n = as.size();
  // top: larger suffix
  int stackLen = 0;
  vector<int> stack(n + 1);
  vector<int> vs(n);
  for (int u = 0; u <= n; ++u) {
    for (; stackLen > 0; --stackLen) {
      const int uu = stack[stackLen - 1];
      const int l = sa.lcp(uu, u);
      if (u + l < n && as[uu + l] > as[u + l]) break;
      vs[uu] = u;
    }
    stack[stackLen++] = u;
  }
  return vs;
}

// (p, [u, v)): run <=>
//   * p: min period of as[u, v)
//   * v - u >= 2 p
//   * [u, v): maximal
// \sum 1 <= n
// \sum (v - u) / p <= 3 n
// \sum (v - u - 2 p + 1) \in O(n log n)  (TODO: proof)

// Returns runs (p, [u, v)) in lex. order.
//   String: string, vector<int>, vector<long long>
//   O(n log n) time, (<= 6 n + 2) SuffixArray::lcp calls
template <class String>
vector<pair<int, pair<int, int>>> repetitions(const String &as, const SuffixArray &sa) {
  assert(sa.rmq);
  const int n = as.size();
  if (n == 0) return {};
  String asRev = as;
  std::reverse(asRev.begin(), asRev.end());
  const SuffixArray saRev(asRev, /*rmq=*/true);
  const vector<int> vs = lyndonPrefix(as, sa);
  const vector<int> vsInverted = lyndonPrefixInverted(as, sa);
  vector<pair<int, pair<int, int>>> runs;
  for (int u = 0; u < n; ++u) {
    // from longest lyndon prefix of as[u, n) or invert(as)[u, n)
    {
      const int v = vs[u];
      const int p = v - u, uu = u - saRev.lcp(n - u, n - v), vv = v + sa.lcp(u, v);
      if (vv - uu >= 2 * p) runs.emplace_back(p, make_pair(uu, vv));
    }
    if (vs[u] != vsInverted[u]) {
      const int v = vsInverted[u];
      const int p = v - u, uu = u - saRev.lcp(n - u, n - v), vv = v + sa.lcp(u, v);
      if (vv - uu >= 2 * p) runs.emplace_back(p, make_pair(uu, vv));
    }
  }
  // radix sort
  const int runsLen = runs.size();
  auto runsWork = runs;
  vector<int> pt(n + 1, 0);
  for (int i = 0; i < runsLen; ++i) ++pt[runs[i].second.first];
  for (int u = 0; u < n - 1; ++u) pt[u + 1] += pt[u];
  for (int i = runsLen; --i >= 0; ) runsWork[--pt[runs[i].second.first]] = runs[i];
  memset(pt.data() + 1, 0, n * sizeof(int));
  for (int i = 0; i < runsLen; ++i) ++pt[runsWork[i].first];
  for (int p = 1; p < n; ++p) pt[p + 1] += pt[p];
  for (int i = runsLen; --i >= 0; ) runs[--pt[runsWork[i].first]] = runsWork[i];
  runs.erase(std::unique(runs.begin(), runs.end()), runs.end());
  return runs;
}
template <class String>
vector<pair<int, pair<int, int>>> repetitions(const String &as) {
  return repetitions(as, SuffixArray(as, /*rmq=*/true));
}

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <string>

using std::cerr;
using std::endl;
using std::string;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

// String: string, vector<int>, vector<long long>
template <class String> void test(const String &as) {
  const int n = as.size();
  vector<vector<String>> substring(n + 1, vector<String>(n + 1));
  for (int u = 0; u <= n; ++u) for (int v = u; v <= n; ++v) {
    substring[u][v] = String(as.begin() + u, as.begin() + v);
  }
  vector<int> us(n + 1, 0);
  for (int v = 1; v <= n; ++v) {
    for (int u = 1; u < v; ++u) if (substring[us[v]][v] > substring[u][v]) {
      us[v] = u;
    }
  }
  vector<vector<int>> isLyndon(n + 1, vector<int>(n + 1));
  for (int u = 0; u < n; ++u) for (int v = u + 1; v <= n; ++v) {
    isLyndon[u][v] = 1;
    for (int w = u + 1; w < v; ++w) if (substring[u][v] > substring[w][v]) {
      isLyndon[u][v] = 0;
      break;
    }
  }
  vector<vector<int>> period(n + 1, vector<int>(n + 1, n + 1));
  for (int p = n; p >= 1; --p) for (int u = 0; u <= n; ++u) {
    for (int v = u; ; ++v) {
      period[u][v] = p;
      if (v == n || (u <= v - p && as[v - p] != as[v])) break;
    }
  }
  auto isRun = [&](int p, int u, int v) -> bool {
    if (period[u][v] != p) return false;
    if (v - u < 2 * p) return false;
    if (0 < u && period[u - 1][v] == p) return false;
    if (v < n && period[u][v + 1] == p) return false;
    return true;
  };
  vector<pair<int, pair<int, int>>> runs;
  for (int p = 1; p <= n; ++p) {
    for (int u = 0; u <= n; ++u) for (int v = u; v <= n; ++v) {
      if (isRun(p, u, v)) {
        runs.emplace_back(p, make_pair(u, v));
      }
    }
  }

  // lyndonSuffix
  {
    const vector<pair<int, int>> pqs = lyndonSuffix(as);
    assert(pqs[0] == make_pair(0, 0));
    for (int v = 1; v <= n; ++v) {
      const int p = v - us[v];
      int q = 1;
      for (int u = v - p; u >= p && substring[u - p][u] == substring[v - p][v]; u -= p) {
        ++q;
      }
      assert(pqs[v] == make_pair(p, q));
    }
  }
  // lyndonPrefix, lyndonPrefixInverted
  {
    const vector<int> vs = lyndonPrefix(as);
    assert(static_cast<int>(vs.size()) == n);
    for (int u = 0; u < n; ++u) {
      int vm = -1;
      for (int v = u + 1; v <= n; ++v) if (isLyndon[u][v]) {
        vm = v;
      }
      assert(vs[u] == vm);
    }
    String asInverted = as;
    if (n > 0) {
      const auto minmaxA = minmax_element(as.begin(), as.end());
      const auto minA = *minmaxA.first, maxA = *minmaxA.second;
      for (int u = 0; u < n; ++u) asInverted[u] = maxA - (asInverted[u] - minA);
    }
    assert(lyndonPrefixInverted(asInverted,
                                SuffixArray(asInverted, /*rmq=*/true)) == vs);
  }
  // repetitions
  assert(repetitions(as) == runs);
}

void testAllVectors(int n, int sigma) {
  vector<int> as(n, 0);
  for (; ; ) {
    test(as);
    for (int i = n; ; ) {
      if (i-- == 0) return;
      if (++as[i] < sigma) break;
      as[i] = 0;
    }
  }
}

void unittest() {
  test(string(""));
  test(string("a"));
  test(string("abracadabra"));
  test(string("sismississippi"));
  test(vector<long long>{-2 * (1LL << 62), 2 * ((1LL << 62) - 1) + 1});
  testAllVectors(0, 1);
  testAllVectors(1, 3);
  testAllVectors(2, 3);
  testAllVectors(3, 5);
  testAllVectors(4, 5);
  testAllVectors(5, 7);
  testAllVectors(6, 7);
  testAllVectors(7, 5);
  testAllVectors(8, 4);
  testAllVectors(9, 4);
  testAllVectors(10, 3);
  testAllVectors(11, 3);
  testAllVectors(12, 2);
  testAllVectors(13, 2);
  testAllVectors(14, 2);
  testAllVectors(15, 2);
  testAllVectors(16, 2);
  testAllVectors(17, 2);
  testAllVectors(18, 2);
  for (int sigma = 1; sigma <= 5; ++sigma) {
    for (int caseId = 0; caseId < 50; ++caseId) {
      vector<long long> cs(sigma);
      for (int a = 0; a < sigma; ++a) {
        cs[a] = xrand() | static_cast<unsigned long long>(xrand()) << 32;
      }
      const int n = xrand() % 50;
      vector<long long> as(n);
      for (int u = 0; u < n; ++u) {
        as[u] = cs[xrand() % sigma];
      }
      test(as);
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
