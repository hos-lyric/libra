#include <utility>
#include <vector>

using std::pair;
using std::swap;
using std::vector;

// (reading(RSK insertion tableau of ps), Knuth transformation)
//   reading: from bottom to top, from left to right
//   Knuth: can swap(ps[i-1], ps[i]) if:
//     ps[i-2] or ps[i+1] has value between ps[i-1] and ps[i]
// ps should be distinct.
template <class T> pair<vector<T>, vector<int>> knuth(vector<T> ps) {
  const int n = ps.size();
  vector<int> ops;
  auto oper = [&](int i) -> void {
    swap(ps[i - 1], ps[i]);
    ops.push_back(i);
  };
  for (int i = 0; i < n; ++i) {
    for (int j = i; j >= 1; ) {
      for (; j >= 2 && ps[j] < ps[j - 2] && ps[j - 2] < ps[j - 1]; --j) oper(j);
      if (ps[j - 1] < ps[j]) break;
      --j;
      for (; j >= 1 && ps[j - 1] < ps[j + 1] && ps[j + 1] < ps[j]; --j) oper(j);
    }
  }
  return std::make_pair(ps, ops);
}

////////////////////////////////////////////////////////////////////////////////

#include <assert.h>
#include <stdio.h>
#include <algorithm>
#include <iostream>

using std::cerr;
using std::endl;
using std::max;
using std::min;

void unittest_knuth() {
  {
    const vector<int> ps{1, 3, 6, 8, 4, 0, 2, 5, 7};
    // 02457
    // 138
    // 6
    const auto res = knuth(ps);
    assert(res.first == (vector<int>{6, 1, 3, 8, 0, 2, 4, 5, 7}));
    assert(res.second == (vector<int>{4,2,1, 5,4,3, 6,5,3, 6,5,4}));
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
      const auto res = knuth(ps);
      assert(res.first == reading);
      auto qs = ps;
      for (const int i : res.second) {
        assert(0 < i); assert(i < n);
        const int mn = min(qs[i - 1], qs[i]);
        const int mx = max(qs[i - 1], qs[i]);
        assert((0 <= i - 2 && mn < qs[i - 2] && qs[i - 2] < mx) |
               (i + 1 <  n && mn < qs[i + 1] && qs[i + 1] < mx));
        swap(qs[i - 1], qs[i]);
      }
      assert(qs == reading);
    } while (next_permutation(ps.begin(), ps.end()));
    cerr << "[unittest_knuth] PASSED n = " << n << endl;
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
  // unittest_knuth(); cerr << "PASSED unittest_knuth" << endl;
  xmas2022c();
  return 0;
}
