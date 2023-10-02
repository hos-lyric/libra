#include <queue>
#include <utility>
#include <vector>

using std::pair;
using std::priority_queue;
using std::vector;

// T: signed integer
// ans[k]: max sum at k non-adjacent indexes  (0 <= k <= ceil(|as|/2))
// ans: concave
template <class T> vector<T> maxNonAdj(const vector<T> &as) {
  const int n = as.size();
  vector<int> del(n + 2, 0), lef(n + 2), rig(n + 2);
  for (int i = 0; i <= n + 1; ++i) {
    lef[i] = i - 1;
    rig[i] = i + 1;
  }
  vector<T> ds(n + 2);
  priority_queue<pair<T, int>> que;
  del[0] = del[n + 1] = 1;
  for (int i = 1; i <= n; ++i) que.emplace(ds[i] = as[i - 1], i);
  vector<T> ans((n + 1) / 2 + 1);
  for (int k = 0; !que.empty(); ) {
    const int i = que.top().second;
    que.pop();
    if (!del[i]) {
      ans[k + 1] = ans[k] + ds[i];
      ++k;
      const int l = lef[i], r = rig[i];
      if (1 <= l) {
        rig[lef[l]] = i;
        lef[i] = lef[l];
      }
      if (r <= n) {
        lef[rig[r]] = i;
        rig[i] = rig[r];
      }
      if (!del[l] && !del[r]) {
        que.emplace(ds[i] = ds[l] + ds[r] - ds[i], i);
      } else {
        del[i] = 1;
      }
      del[l] = del[r] = 1;
    }
  }
  return ans;
}

////////////////////////////////////////////////////////////////////////////////

#include <assert.h>
#include <stdio.h>
#include <algorithm>
#include <iostream>

using std::cerr;
using std::endl;
using std::max;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

template <class T> vector<T> brute(const vector<T> &as, T inf) {
  const int n = as.size();
  vector<vector<T>> dp(n + 1, vector<T>((n + 1) / 2 + 1, -inf));
  dp[0][0] = 0;
  for (int i = 0; i < n; ++i) {
    dp[i + 1] = dp[i];
    for (int k = 1; k <= (n + 1) / 2; ++k) {
      if (dp[i + 1][k] < dp[max(i - 1, 0)][k - 1] + as[i]) {
        dp[i + 1][k] = dp[max(i - 1, 0)][k - 1] + as[i];
      }
    }
  }
  return dp[n];
}
void unittest() {
  for (int n = 0; n <= 6; ++n) {
    // [0, 8)^n
    for (int p = 0; p < 1 << (3 * n); ++p) {
      vector<int> as(n);
      for (int i = 0; i < n; ++i) as[i] = (p >> (3 * i) & 7) - 4;
      const vector<int> expected = brute(as, 1001001001);
      const vector<int> actual = maxNonAdj(as);
      assert(expected == actual);
      for (int k = 0; k + 2 <= (n + 1) / 2; ++k) {
        assert(actual[k + 1] - actual[k] >= actual[k + 2] - actual[k + 1]);
      }
    }
  }
  for (int caseId = 0; caseId < 100; ++caseId) {
    const int n = 1 + xrand() % 100;
    vector<long long> as(n);
    for (int i = 0; i < n; ++i) as[i] = static_cast<int>(xrand());
    const vector<long long> expected = brute(as, 100100100100100101LL);
    const vector<long long> actual = maxNonAdj(as);
    assert(expected == actual);
    for (int k = 0; k + 2 <= (n + 1) / 2; ++k) {
      assert(actual[k + 1] - actual[k] >= actual[k + 2] - actual[k + 1]);
    }
  }
}

// https://qoj.ac/contest/365/problem/123
// https://atcoder.jp/contests/joisc2018/tasks/joisc2018_j
void joisc2018_candies() {
  int N;
  for (; ~scanf("%d", &N); ) {
    vector<long long> A(N);
    for (int i = 0; i < N; ++i) scanf("%lld", &A[i]);
    const vector<long long> ans = maxNonAdj(A);
    for (int k = 1; k <= (N + 1) / 2; ++k) printf("%lld\n", ans[k]);
    for (int k = 0; k + 2 <= (N + 1) / 2; ++k) {
      assert(ans[k + 1] - ans[k] >= ans[k + 2] - ans[k + 1]);
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // joisc2018_candies();
  return 0;
}
