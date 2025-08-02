#include <algorithm>
#include <utility>
#include <vector>

using std::max;
using std::min;
using std::pair;
using std::vector;

// rectss[a] = [((l0, l1), (r0, r1))]
//   mex(as[l, r)) = a  for  l0 <= l < l1, r0 <= r < r1
// \sum[0<=a<=n] |rectss[a]| <= 3 n + 1
//   number of calls to add
//     - extend existing interval at most once for each l
//     - otherwise create new open rectangle
//   number of open rectangles (l0 not determined)
//     - decreases by at most 1 for each l
//     - remains <= n + 1
vector<vector<pair<pair<int, int>, pair<int, int>>>> allRangeMex(const vector<int> &as) {
  const int n = as.size();
  // maintain range max
  int segN;
  for (segN = 1; segN < n + 1; segN <<= 1) {}
  vector<int> seg(segN << 1, n);
  auto segChange = [&](int a, int i) -> void {
    for (seg[a += segN] = i; a >>= 1; ) seg[a] = max(seg[a << 1], seg[a << 1 | 1]);
  };
  // min a s.t. seg[a] >= i
  auto segFind = [&](int i) -> int {
    for (int a = 1; ; a = (seg[a << 1] >= i) ? (a << 1) : (a << 1 | 1)) if (a >= segN) return a - segN;
  };
  // l0 = 0 for open rectangle
  vector<vector<pair<pair<int, int>, pair<int, int>>>> rectss(n + 1);
  auto add = [&](int a, int l1, int r0, int r1) -> void {
    if (rectss[a].size() && !rectss[a].back().first.first) {
      rectss[a].back().first.first = l1;
      if (r1 == rectss[a].back().second.first) r1 = rectss[a].back().second.second;
    }
    rectss[a].emplace_back(std::make_pair(0, l1), std::make_pair(r0, r1));
  };
  // as[n, n)
  add(0, n + 1, n, n + 1);
  for (int l = n; --l >= 0; ) {
    if (0 <= as[l] && as[l] < n) {
      segChange(as[l], l);
      if (rectss[as[l]].size() && !rectss[as[l]].back().first.first) {
        // erase interval r0 <= r < r1 (previously mex = as[l])
        rectss[as[l]].back().first.first = l + 1;
        const int r0 = rectss[as[l]].back().second.first;
        const int r1 = rectss[as[l]].back().second.second;
        for (int r = r0; r < r1; ) {
          const int a = segFind(r);
          const int rr = min(seg[segN + a] + 1, r1);
          // adding interval, or extending existing interval at most once
          add(a, l + 1, r, rr);
          r = rr;
        }
      }
    }
    // as[l, l)
    add(0, l + 1, l, l + 1);
  }
  return rectss;
}

////////////////////////////////////////////////////////////////////////////////

#include <assert.h>
#include <stdio.h>
#include <iostream>
#include <random>
#include <set>

using std::cerr;
using std::endl;
using std::mt19937_64;
using std::set;

void unittest() {
  //  012013201
  // r
  // ^4444443200
  // |444441110
  // |44440000
  // |4442000
  // |333200
  // |33110
  // |3000
  // |200
  // |10
  // |0
  //  --------->l
  assert(allRangeMex({0, 1, 2, 0, 1, 3, 2, 0, 1}) ==
         (vector<vector<pair<pair<int, int>, pair<int, int>>>>{
    /*0*/ {{{9, 10}, {9, 10}}, {{8, 9}, {8, 10}}, {{7, 8}, {7, 8}}, {{6, 7}, {6, 8}}, {{5, 6}, {5, 8}}, {{4, 5}, {4, 8}}, {{3, 4}, {3, 4}}, {{2, 3}, {2, 4}}, {{1, 2}, {1, 4}}, {{0, 1}, {0, 1}}},
    /*1*/ {{{5, 8}, {8, 9}}, {{2, 4}, {4, 5}}, {{0, 1}, {1, 2}}},
    /*2*/ {{{7, 8}, {9, 10}}, {{3, 4}, {5, 7}}, {{0, 1}, {2, 3}}},
    /*3*/ {{{6, 7}, {9, 10}}, {{2, 3}, {5, 6}}, {{1, 2}, {4, 6}}, {{0, 1}, {3, 6}}},
    /*4*/ {{{5, 6}, {9, 10}}, {{4, 5}, {8, 10}}, {{3, 4}, {7, 10}}, {{0, 3}, {6, 10}}},
    /*5*/ {},
    /*6*/ {},
    /*7*/ {},
    /*8*/ {},
    /*9*/ {},
  }));

  auto test = [&](const vector<int> &as) -> void {
    const int n = as.size();
    vector<vector<int>> mex(n + 1, vector<int>(n + 1, -1));
    for (int l = 0; l <= n; ++l) {
      set<int> app;
      for (int r = l; r <= n; ++r) {
        for (int &a = mex[l][r] = 0; app.count(a); ++a) {}
        if (r < n) app.insert(as[r]);
      }
    }
    const auto rectss = allRangeMex(as);
    assert(rectss.size() == static_cast<size_t>(n + 1));
    int numRects = 0;
    for (int a = 0; a <= n; ++a) for (const auto &rect : rectss[a]) {
      ++numRects;
      for (int l = rect.first.first; l < rect.first.second; ++l) {
        for (int r = rect.second.first; r < rect.second.second; ++r) {
          assert(l <= r);
          assert(mex[l][r] == a);
        }
      }
    }
    assert(numRects <= 3 * n + 1);
  };
  for (int n = 0; n <= 8; ++n) {
    // [0, 8)^n
    for (int p = 0; p < 1 << (3 * n); ++p) {
      vector<int> as(n);
      for (int i = 0; i < n; ++i) as[i] = p >> (3 * i) & 7;
      test(as);
    }
    cerr << "[unittest] PASSED n = " << n << endl;
  }
  mt19937_64 rng;
  for (int n = 9; n <= 100; ++n) {
    vector<int> as(n);
    for (int i = 0; i < n; ++i) as[i] = rng() % (n + 1);
    test(as);
  }
}

// https://qoj.ac/contest/1454/problem/7969
void qoj7969() {
  int N;
  for (; ~scanf("%d", &N); ) {
    vector<int> A(N);
    for (int i = 0; i < N; ++i) {
      scanf("%d", &A[i]);
    }
    const auto rectss = allRangeMex(A);
    vector<vector<int>> addss(N + 1), remss(N + 1);
    for (int a = 0; a <= N; ++a) for (const auto &rect : rectss[a]) {
      addss[rect.second.first - (rect.first.second - 1)].push_back(a);
      remss[(rect.second.second - 1) - rect.first.first].push_back(a);
    }
    vector<int> freq(N + 1, 0);
    set<int> ex;
    for (int a = 0; a <= N + 1; ++a) ex.insert(a);
    vector<int> ans(N + 1);
    for (int k = 0; k <= N; ++k) {
      for (const int a : addss[k]) if (!freq[a]++) ex.erase(a);
      ans[k] = *ex.begin();
      for (const int a : remss[k]) if (!--freq[a]) ex.insert(a);
    }
    for (int k = 1; k <= N; ++k) {
      if (k > 1) printf(" ");
      printf("%d", ans[k]);
    }
    puts("");
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // qoj7969();
  return 0;
}
