#include "suffix_array.h"

#include <algorithm>
#include <assert.h>
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
  vector<String> suffix(n);
  for (int u = 0; u < n; ++u) suffix[u] = String(as.begin() + u, as.end());
  vector<int> brt(n);
  for (int u = 0; u < n; ++u) brt[u] = u;
  std::sort(brt.begin(), brt.end(), [&](int u, int v) -> bool {
    return (suffix[u] < suffix[v]);
  });
  vector<vector<int>> lcp(n + 1, vector<int>(n + 1, 0));
  for (int u = n; --u >= 0; ) for (int v = n; --v >= 0; ) {
    lcp[u][v] = (as[u] == as[v]) ? (1 + lcp[u + 1][v + 1]) : 0;
  }

  // suffixArrayRec
  {
    const vector<int> us = suffixArrayRec(as);
    assert(us == brt);
  }
  // SuffixArray(as, rmq=false)
  {
    const SuffixArray sa(as, false);
    assert(sa.n == n);
    assert(!sa.rmq);
    assert(sa.us == brt);
    assert(static_cast<int>(sa.su.size()) == n + 1);
    for (int u = 0; u < n; ++u) assert(sa.su[brt[u]] == u);
    assert(sa.su[n] == -1);
    assert(static_cast<int>(sa.hs.size()) == n);
    for (int i = 0; i < n; ++i) {
      assert(sa.hs[i] == lcp[i ? brt[i - 1] : n][brt[i]]);
    }
  }
  // SuffixArray(as, rmq=true)
  {
    const SuffixArray sa(as, true);
    assert(sa.n == n);
    assert(sa.rmq);
    assert(sa.us == brt);
    assert(static_cast<int>(sa.su.size()) == n + 1);
    for (int u = 0; u < n; ++u) assert(sa.su[brt[u]] == u);
    assert(sa.su[n] == -1);
    assert(static_cast<int>(sa.hs.size()) >= n);
    for (int i = 0; i < n; ++i) {
      assert(sa.hs[i] == lcp[i ? brt[i - 1] : n][brt[i]]);
    }
    for (int u = 0; u < n; ++u) for (int v = 0; v < n; ++v) {
      assert(sa.lcp(u, v) == lcp[u][v]);
    }
  }
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
  for (int sigma = 1; sigma <= 10; ++sigma) {
    for (int caseId = 0; caseId < 100; ++caseId) {
      vector<long long> cs(sigma);
      for (int a = 0; a < sigma; ++a) {
        cs[a] = xrand() | static_cast<unsigned long long>(xrand()) << 32;
      }
      const int n = xrand() % 100;
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
