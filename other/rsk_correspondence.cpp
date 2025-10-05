#include <assert.h>
#include <utility>
#include <vector>

using std::pair;
using std::swap;
using std::vector;

// Returns (reading(RSK insertion tableau of ps), Knuth transformation).
//   reading: from bottom to top, from left to right
//   Knuth: can swap(ps[i-1], ps[i]) if:
//     ps[i-2] or ps[i+1] has value between ps[i-1] and ps[i]
// ps must be distinct.
// O(n^2) time.
template <class T> pair<vector<T>, vector<int>> knuth(vector<T> ps) {
  const int n = ps.size();
  vector<int> ops;
  auto oper = [&](int i) -> void {
    swap(ps[i - 1], ps[i]);
    ops.push_back(i);
  };
  for (int i = 0; i < n; ++i) {
    for (int j = i; ; ) {
      if (j == 0 || ps[j - 1] < ps[j]) break;
      for (; j >= 2 && ps[j] < ps[j - 2] && ps[j - 2] < ps[j - 1]; --j) oper(j);
      --j;
      for (; j >= 1 && ps[j - 1] < ps[j + 1] && ps[j + 1] < ps[j]; --j) oper(j);
    }
  }
  return std::make_pair(ps, ops);
}

// Finds k disjoint increasing subsequences, maximizing the size of the union.
// ps must be a permutation of (0, 1, ..., n-1).
// O(n^2) time.
template <class T> vector<vector<int>> kIncrSubseqs(vector<T> ps, int k) {
  const int n = ps.size();
  vector<int> invP(n, -1);
  for (int i = 0; i < n; ++i) {
    assert(0 <= ps[i]); assert(ps[i] < n);
    assert(!~invP[ps[i]]);
    invP[ps[i]] = i;
  }
  assert(k >= 0);
  // Knuth transformation
  vector<int> poss(n);
  for (int i = 0; i < n; ++i) {
    for (int j = i; ; ) {
      if (j == 0 || ps[j - 1] < ps[j]) {
        poss[i] = j;
        break;
      }
      for (; j >= 2 && ps[j] < ps[j - 2] && ps[j - 2] < ps[j - 1]; --j) swap(ps[j - 1], ps[j]);
      --j;
      for (; j >= 1 && ps[j - 1] < ps[j + 1] && ps[j + 1] < ps[j]; --j) swap(ps[j - 1], ps[j]);
    }
  }
  // initial solution: top k rows of RSK insertion tableau
  // -1: null, -2: not used
  vector<int> lef(n, -2), rig(n, -2);
  for (int kk = k, i = n; kk > 0 && i > 0; --kk) {
    rig[ps[i - 1]] = -1;
    for (; --i >= 1 && ps[i - 1] < ps[i]; ) {
      rig[ps[i - 1]] = ps[i];
      lef[ps[i]] = ps[i - 1];
    }
    lef[ps[i]] = -1;
  }
  // rewind Knuth transformation
  for (int i = n; --i >= 0; ) {
    for (int j = poss[i]; j < i; ) {
      for (; j + 2 <= i && ps[j + 1] < ps[j + 2] && ps[j + 2] < ps[j]; ++j) {
        // a<b<c, cab -> acb; still valid
        swap(ps[j], ps[j + 1]);
      }
      ++j;
      for (; j + 1 <= i && ps[j] < ps[j - 1] && ps[j - 1] < ps[j + 1]; ++j) {
        // a<b<c, bac -> bca, invalid if we are using a<c
        const int a = ps[j], b = ps[j - 1], c = ps[j + 1];
        if (rig[a] == c) {
          if (lef[b] != -2) {
            // a<c<..., ...<b<... -> b<c<..., ...<a<...
            if (~rig[b]) lef[rig[b]] = a;
            lef[c] = b;
            swap(rig[a], rig[b]);
          } else {
            // ...<a<c -> ...<b<c
            if (~lef[a]) rig[lef[a]] = b;
            lef[c] = b;
            swap(lef[a], lef[b]);
            swap(rig[a], rig[b]);
          }
        }
        swap(ps[j], ps[j + 1]);
      }
    }
  }
  vector<vector<int>> iss;
  for (int a = 0; a < n; ++a) if (!~lef[a]) {
    iss.emplace_back();
    for (int b = a; ~b; b = rig[b]) iss.back().push_back(invP[b]);
  }
  iss.resize(k, {});
  return iss;
}

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <algorithm>
#include <iostream>

using std::cerr;
using std::endl;
using std::max;
using std::min;

void unittest() {
  {
    const vector<int> ps{1, 3, 6, 8, 4, 0, 2, 5, 7};
    // 02457
    // 138
    // 6
    const auto resKnuth = knuth(ps);
    assert(resKnuth.first == (vector<int>{6, 1,3,8, 0,2,4,5,7}));
    assert(resKnuth.second == (vector<int>{4,2,1, 5,4,3, 6,5,3, 6,5,4}));
    assert(kIncrSubseqs(ps, 0) == (vector<vector<int>>{}));
    assert(kIncrSubseqs(ps, 1) == (vector<vector<int>>{{0, 1, 4, 7, 8}}));
    assert(kIncrSubseqs(ps, 2) == (vector<vector<int>>{{5, 6, 7, 8}, {0, 1, 2, 3}}));
    assert(kIncrSubseqs(ps, 10) == (vector<vector<int>>{{5, 6, 7, 8}, {0, 1, 4}, {2, 3}, {}, {}, {}, {}, {}, {}, {}}));
  }
  for (int n = 0; n <= 10; ++n) {
    vector<int> ps(n);
    for (int i = 0; i < n; ++i) ps[i] = i;
    do {
      vector<vector<int>> tab(n);
      for (int i = 0; i < n; ++i) {
        int p = ps[i];
        for (int x = 0; x < n; ++x) {
          auto it = std::lower_bound(tab[x].begin(), tab[x].end(), p);
          if (it != tab[x].end()) {
            swap(*it, p);
          } else {
            tab[x].push_back(p);
            break;
          }
        }
      }
      vector<int> reading;
      for (int x = n; --x >= 0; ) for (const int p : tab[x]) reading.push_back(p);
      const auto resKnuth = knuth(ps);
      assert(resKnuth.first == reading);
      auto qs = ps;
      for (const int i : resKnuth.second) {
        assert(0 < i); assert(i < n);
        const int mn = min(qs[i - 1], qs[i]);
        const int mx = max(qs[i - 1], qs[i]);
        assert((0 <= i - 2 && mn < qs[i - 2] && qs[i - 2] < mx) |
               (i + 1 <  n && mn < qs[i + 1] && qs[i + 1] < mx));
        swap(qs[i - 1], qs[i]);
      }
      assert(qs == reading);
      vector<int> scores(n + 1, 0);
      for (int x = 0; x < n; ++x) scores[x + 1] = scores[x] + static_cast<int>(tab[x].size());
      for (int k = 0; k <= n; ++k) {
        const auto iss = kIncrSubseqs(ps, k);
        assert(static_cast<int>(iss.size()) == k);
        vector<int> used(n, 0);
        int sum = 0;
        for (int x = 0; x < k; ++x) {
          int bef = -1;
          for (const int i : iss[x]) {
            assert(0 <= i); assert(i < n);
            assert(!used[i]);
            used[i] = 1;
            assert(bef < ps[i]);
            bef = ps[i];
          }
          sum += static_cast<int>(iss[x].size());
        }
        assert(sum == scores[k]);
      }
    } while (next_permutation(ps.begin(), ps.end()));
    cerr << "[unittest] PASSED n = " << n << endl;
  }
}

// https://atcoder.jp/contests/xmascon22/tasks/xmascon22_c
void xmas2022c() {
  int N;
  for (; ~scanf("%d", &N); ) {
    vector<int> P(N), Q(N);
    for (int i = 0; i < N; ++i) { scanf("%d", &P[i]); --P[i]; }
    for (int i = 0; i < N; ++i) { scanf("%d", &Q[i]); --Q[i]; }
    const auto resP = knuth(P);
    const auto resQ = knuth(Q);
    if (resP.first == resQ.first) {
      auto ans = resP.second;
      for (int k = resQ.second.size(); --k >= 0; ) ans.push_back(resQ.second[k]);
      const int ansLen = ans.size();
      printf("%d\n", ansLen);
      for (int k = 0; k < ansLen; ++k) {
        if (k) printf(" ");
        printf("%d", ans[k]);
      }
      puts("");
    } else {
      puts("-1");
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // xmas2022c();
  return 0;
}
