#include <assert.h>
#include <algorithm>
#include <utility>
#include <vector>

using std::max;
using std::pair;
using std::vector;

// Returns (true, 01 vector of length n) or (false, []).
// O(n (max(as))) time, O(n (max(as))) space
pair<bool, vector<int>> subsetSum(const vector<int> &as, int b) {
  const int n = as.size();
  for (int i = 0; i < n; ++i) assert(as[i] >= 0);
  int sumA = 0;
  for (int i = 0; i < n; ++i) sumA += as[i];
  if (!(0 <= b && b <= sumA)) return std::make_pair(false, vector<int>{});
  // flip, sort for constant-factor (to reduce n-k, mL)
  const bool flipped = (b < sumA - b);
  if (flipped) b = sumA - b;
  vector<pair<int, int>> ps(n);
  for (int i = 0; i < n; ++i) ps[i] = std::make_pair(as[i], i);
  std::sort(ps.begin(), ps.end());
  int k;
  for (k = 0; k < n; ++k) {
    if (b < ps[k].first) break;
    b -= ps[k].first;
  }
  if (b == 0) {
    vector<int> ans(n, 0);
    for (int i = 0; i < k; ++i) ans[ps[i].second] = 1;
    if (flipped) for (int i = 0; i < n; ++i) ans[i] ^= 1;
    return std::make_pair(true, ans);
  }
  // dp[j][x] (k <= j <= n, -mL <= x <= mR): max i to have balance x with:
  //   [0, i): keep
  //   [i, k): keep or discard
  //   [k, j): ignore or use
  //   [j, n): ignore
  const int mL = ps[k].first, mR = ps[n - 1].first;
  vector<int> buffer((n - k + 1) * (mL + 1 + mR), -1);
  vector<int *> dp(n + 1);
  for (int j = k; j <= n; ++j) dp[j] = buffer.data() + ((j - k) * (mL + 1 + mR) + mL);
  dp[k][-b] = k;
  for (int j = k; j < n; ++j) {
    for (int x = -mL; x <= mR; ++x) dp[j + 1][x] = dp[j][x];
    // use
    for (int x = -mL; x < 0; ++x) {
      const int xx = x + ps[j].first;
      if (dp[j + 1][xx] < dp[j][x]) dp[j + 1][xx] = dp[j][x];
    }
    // discard
    for (int x = mR; x > 0; --x) {
      for (int i = max(dp[j][x], 0); i < dp[j + 1][x]; ++i) {
        const int xx = x - ps[i].first;
        if (dp[j + 1][xx] < i) dp[j + 1][xx] = i;
      }
    }
    // recover
    if (dp[j + 1][0] >= 0) {
      vector<int> ans(n, 0);
      for (int i = 0; i < k; ++i) ans[ps[i].second] = 1;
      for (int x = 0; x != -b; ) {
        for (; dp[j][x] >= dp[j + 1][x]; --j) {}
        const int xx = x - ps[j].first;
        if (xx >= -mL && dp[j][xx] >= dp[j + 1][x]) {
          ans[ps[j].second] = 1;
          x = xx;
          --j;
          continue;
        }
        const int i = dp[j + 1][x];
        ans[ps[i].second] = 0;
        x += ps[i].first;
      }
      if (flipped) for (int i = 0; i < n; ++i) ans[i] ^= 1;
      return std::make_pair(true, ans);
    }
  }
  return std::make_pair(false, vector<int>{});
}

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <random>

using std::cerr;
using std::endl;
using std::mt19937_64;

void unittest() {
  mt19937_64 rng;
  for (int n = 0; n <= 100; ++n) {
    for (int caseId = 0; caseId < 100; ++caseId) {
      const int lim = rng() % 100;
      vector<int> as(n);
      for (int i = 0; i < n; ++i) as[i] = rng() % (lim + 1);
      vector<int> dp(n * lim + 1, 0);
      dp[0] = 1;
      for (int i = 0; i < n; ++i) for (int x = i * lim; x >= 0; --x) if (dp[x]) dp[x + as[i]] = 1;
      for (int b = 0; b <= n * lim; ++b) {
        const pair<bool, vector<int>> res = subsetSum(as, b);
        if (dp[b]) {
          assert(res.first);
          assert(static_cast<int>(res.second.size()) == n);
          int sum = 0;
          for (int i = 0; i < n; ++i) {
            assert(res.second[i] == 0 || res.second[i] == 1);
            if (res.second[i]) sum += as[i];
          }
          assert(sum == b);
        } else {
          assert(!res.first);
        }
      }
    }
    cerr << "[unittest] PASSED n = " << n << endl;
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
