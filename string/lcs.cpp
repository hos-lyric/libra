#include <algorithm>
#include <utility>
#include <vector>

using std::pair;
using std::vector;

// LCS: longest common (not necessarily contiguous) subsequence
// (i  ,j)->(i  ,j+1): 0...000...01
// [as[i] = bs[j]]   : 0...01*...**
// (i+1,j)->(i+1,j+1): 0...010...00
template <class String> int lcs(const String &as, const String &bs) {
  const int m = as.size(), n = bs.size();
  String cs = as;
  cs.insert(cs.end(), bs.begin(), bs.end());
  std::sort(cs.begin(), cs.end());
  cs.erase(std::unique(cs.begin(), cs.end()), cs.end());
  const int csLen = cs.size();
  const int len = (n + 63 - 1) / 63;
  vector<unsigned long long> match(csLen * len, 0ULL);
  for (int j = 0; j < n; ++j) {
    const int b = std::lower_bound(cs.begin(), cs.end(), bs[j]) - cs.begin();
    match[b * len + (j / 63)] |= 1ULL << (j % 63);
  }
  vector<unsigned long long> dp(len, 0ULL);
  for (int i = 0; i < m; ++i) {
    const int a = std::lower_bound(cs.begin(), cs.end(), as[i]) - cs.begin();
    unsigned long long carry = 0;
    for (int k = 0; k < len; ++k) {
      const unsigned long long f = match[a * len + k];
      const unsigned long long g = dp[k] - carry - (~dp[k] & f);
      (dp[k] |= f) &= g;
      carry = g >> 63;
    }
  }
  int ans = 0;
  for (int k = 0; k < len; ++k) ans += __builtin_popcountll(dp[k]);
  return ans;
}

// LCS: longest common (not necessarily contiguous) subsequence
// \Delta[k] LCS(as[0, k), bs[l, r)) = [l <  f[k][r]]
// \Delta[r] LCS(as[0, k), bs[l, r)) = [l >= g[k][r]]
struct PreSubLCS {
  int m, n;
  vector<vector<int>> f, g;
  int id;
  vector<vector<vector<pair<int, int>>>> lqsss;
  vector<int> anss;
  template <class String> void build(const String &as, const String &bs) {
    m = as.size();
    n = bs.size();
    f.assign(m, vector<int>(n + 1, 0));
    g.assign(m + 1, vector<int>(n, 0));
    for (int r = 0; r < n; ++r) g[0][r] = r + 1;
    for (int k = 0; k < m; ++k) for (int r = 0; r < n; ++r) {
      if (as[k] == bs[r] || f[k][r] > g[k][r]) {
        f[k][r + 1] = g[k][r];
        g[k + 1][r] = f[k][r];
      } else {
        f[k][r + 1] = f[k][r];
        g[k + 1][r] = g[k][r];
      }
    }
    id = 0;
    lqsss.assign(m + 1, vector<vector<pair<int, int>>>(n + 1));
  }
  void get(int k, int l, int r) {
    lqsss[k][r].emplace_back(l, id++);
  }
  void run() {
    anss.resize(id);
    for (int k = 0; k <= m; ++k) {
      vector<int> bit(n + 1, 0);
      for (int r = 0; ; ++r) {
        for (const pair<int, int> &lq : lqsss[k][r]) {
          int sum = 0;
          for (int x = lq.first + 1; x; x &= x - 1) sum += bit[x - 1];
          anss[lq.second] = sum - lq.first;
        }
        if (r == n) break;
        for (int x = g[k][r]; x <= n; x |= x + 1) ++bit[x];
      }
    }
  }
};
template <class String> PreSubLCS preSubLCS(const String &as, const String &bs) {
  PreSubLCS psl;
  psl.build(as, bs);
  return psl;
}

////////////////////////////////////////////////////////////////////////////////

#include <assert.h>
#include <stdio.h>
#include <iostream>
#include <random>
#include <string>

using std::cerr;
using std::endl;
using std::mt19937_64;
using std::string;

template <class T> bool chmax(T &t, const T &f) { if (t < f) { t = f; return true; } return false; }

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

template <class String> void test(const String &as, const String &bs, int numQueries) {
  PreSubLCS psl = preSubLCS(as, bs);
  const int m = as.size(), n = bs.size();
  vector<vector<vector<int>>> dp(m + 1, vector<vector<int>>(n + 1, vector<int>(n + 1, 0)));
  for (int k = 0; k <= m; ++k) for (int l = 0; l <= n; ++l) for (int r = l; r <= n; ++r) {
    if (k < m) chmax(dp[k + 1][l][r], dp[k][l][r]);
    if (r < n) chmax(dp[k][l][r + 1], dp[k][l][r]);
    if (k < m && r < n && as[k] == bs[r]) chmax(dp[k + 1][l][r + 1], dp[k][l][r] + 1);
  }
  assert(dp[m][0][n] == lcs(as, bs));
  for (int k = 0; k < m; ++k) for (int r = 0; r <= n; ++r) {
    assert(0 <= psl.f[k][r]); assert(psl.f[k][r] <= r);
    for (int l = 0; l <= r; ++l) {
      assert(dp[k + 1][l][r] - dp[k][l][r] == ((l < psl.f[k][r]) ? 1 : 0));
    }
  }
  for (int k = 0; k <= m; ++k) for (int r = 0; r < n; ++r) {
    assert(0 <= psl.g[k][r]); assert(psl.g[k][r] <= r + 1);
    for (int l = 0; l <= r; ++l) {
      assert(dp[k][l][r + 1] - dp[k][l][r] == ((l >= psl.g[k][r]) ? 1 : 0));
    }
  }
  vector<int> expected;
  if (~numQueries) {
    for (int q = 0; q < numQueries; ++q) {
      const int k = xrand() % (m + 1);
      for (; ; ) {
        const int l = xrand() % (n + 1);
        const int r = xrand() % (n + 1);
        if (l <= r) {
          expected.push_back(dp[k][l][r]);
          psl.get(k, l, r);
          break;
        }
      }
    }
  } else {
    for (int k = 0; k <= m; ++k) for (int l = 0; l <= n; ++l) for (int r = l; r <= n; ++r) {
      expected.push_back(dp[k][l][r]);
      psl.get(k, l, r);
    }
  }
  psl.run();
  assert(expected == psl.anss);
}

void unittest() {
  test(string("test"), string("set"), -1);

  // Alves, Caceres, Song, An all-substrings common subsequence algorithm
  test(string("yxxyzyzx"), string("yxxyzxyzxyxzx"), -1);

  for (int m = 0; m <= 4; ++m) for (int n = 0; n <= 4; ++n) {
    for (int p = 0; p < 1 << (2 * m); ++p) for (int q = 0; q < 1 << (2 * n); ++q) {
      vector<int> as(m), bs(n);
      for (int i = 0; i < m; ++i) as[i] = p >> (2 * i) & 3;
      for (int j = 0; j < n; ++j) bs[j] = q >> (2 * j) & 3;
      test(as, bs, -1);
    }
    cerr << "[unittest] DONE sigma = 4, m = " << m << ", n = " << n << endl;
  }
  for (int m = 5; m <= 8; ++m) for (int n = 5; n <= 8; ++n) {
    for (int p = 0; p < 1 << m; ++p) for (int q = 0; q < 1 << n; ++q) {
      vector<int> as(m), bs(n);
      for (int i = 0; i < m; ++i) as[i] = p >> i & 1;
      for (int j = 0; j < n; ++j) bs[j] = q >> j & 1;
      test(as, bs, 58);
    }
    cerr << "[unittest] DONE sigma = 2, m = " << m << ", n = " << n << endl;
  }

  {
    mt19937_64 rng;
    for (int caseId = 0; caseId < 100; ++caseId) {
      const int m = rng() % 201;
      const int n = rng() % 201;
      vector<long long> as(m), bs(n);
      for (int i = 0; i < m; ++i) as[i] = rng();
      for (int j = 0; j < n; ++j) bs[j] = rng();
      test(as, bs, 10);
    }
    cerr << "[unittest] DONE random cases" << endl;
  }
}

// https://loj.ac/p/6564
void loj_6564() {
  int M, N;
  for (; ~scanf("%d%d", &M, &N); ) {
    vector<int> A(M), B(N);
    for (int i = 0; i < M; ++i) scanf("%d", &A[i]);
    for (int j = 0; j < N; ++j) scanf("%d", &B[j]);
    const int ans = lcs(A, B);
    printf("%d\n", ans);
  }
}

// https://judge.yosupo.jp/problem/prefix_substring_lcs
void yosupo_prefix_substring_lcs() {
  int Q;
  char S[1001], T[1001];
  for (; ~scanf("%d", &Q); ) {
    scanf("%s", S);
    scanf("%s", T);
    auto psl = preSubLCS(string(S), string(T));
    for (int q = 0; q < Q; ++q) {
      int k, l, r;
      scanf("%d%d%d", &k, &l, &r);
      psl.get(k, l, r);
    }
    psl.run();
    for (int q = 0; q < Q; ++q) {
      printf("%d\n", psl.anss[q]);
    }
  }
}

int main() {
  // unittest(); cerr << "PASSED unittest" << endl;
  // yosupo_prefix_substring_lcs();
  loj_6564();
  return 0;
}
