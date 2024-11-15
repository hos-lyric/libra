#include <assert.h>
#include <utility>
#include <vector>

using std::pair;
using std::vector;

// dp[0, n]
// dp[r].first = min[0<=l<r] (dp[l].first + cost(l, r))
// dp[r].second: number of steps (tie-break: min)
// recover: n -> prv[n] -> prv[prv[n]] -> ... -> 0
// cost(l, r) must be totally monotone:
// O(n log(n)) time
//   given l0 < l1, for l1 < r,
//   r -> [cost(l0, r) < cost(l1, r)]: decreasing
//   binary search to find boundary
template <class T> struct MonotoneMinDP {
  vector<pair<T, int>> dp;
  vector<int> prv;
  vector<pair<int, int>> que;
  template <class Cost> pair<T, int> operator()(int n, Cost cost) {
    assert(n >= 0);
    auto get = [&](int l, int r) -> pair<T, int> {
      return std::make_pair(dp[l].first + cost(l, r), dp[l].second + 1);
    };
    dp.resize(n + 1);
    prv.resize(n + 1);
    que.resize(n + 1);
    dp[0] = std::make_pair(T(), 0);
    prv[0] = -1;
    if (n == 0) return std::make_pair(T(), 0);
    // que[head, tail)
    // from que[k].first to [que[k].second, que[k + 1].second)
    int head = 0, tail = 1;
    que[0] = std::make_pair(0, 1);
    for (int i = 1; ; ++i) {
      dp[i] = get(prv[i] = que[head].first, i);
      if (i == n) break;
      ++que[head].second;
      if (head + 1 < tail && que[head].second == que[head + 1].second) ++head;
      for (int rr = n + 1; ; --tail) {
        if (head == tail) {
          que[tail++] = std::make_pair(i, i + 1);
          break;
        }
        const int l = que[tail - 1].first, r = que[tail - 1].second;
        if (get(l, r) < get(i, r)) {
          int lo = r, hi = rr;
          for (; lo + 1 < hi; ) {
            const int mid = (lo + hi) / 2;
            ((get(l, mid) < get(i, mid)) ? lo : hi) = mid;
          }
          if (hi <= n) que[tail++] = std::make_pair(i, hi);
          break;
        } else {
          rr = r;
        }
      }
    }
    return dp[n];
  }
};  // MonotoneMinDP

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <random>

using std::cerr;
using std::endl;
using std::mt19937_64;

void unittest() {
  mt19937_64 rng;
  MonotoneMinDP<long long> f;
  for (int caseId = 0; caseId < 10; ++caseId) for (int n = 0; n <= 100; ++n) {
    vector<long long> xs(n + 1, 0);
    for (int i = 0; i < n; ++i) xs[i + 1] = xs[i] + rng() % (1LL << 20);
    const long long a = rng() % (xs[n] + 1);
    auto cost = [&](int l, int r) -> long long {
      const long long d = (xs[r] - xs[l]) - a;
      return d * d;
    };
    vector<pair<long long, int>> dp(n + 1, std::make_pair(1LL << 60, 0));
    vector<int> prv(n + 1, -1);
    dp[0] = std::make_pair(0, 0);
    for (int l = 0; l < n; ++l) for (int r = l + 1; r <= n; ++r) {
      const pair<long long, int> t(dp[l].first + cost(l, r), dp[l].second + 1);
      if (dp[r] > t) {
        dp[r] = t;
        prv[r] = l;
      }
    }
    f(n, cost);
    assert(f.dp == dp);
    assert(f.prv == prv);
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
