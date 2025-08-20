#include <assert.h>
#include <algorithm>
#include <vector>

using std::vector;

template <class T> struct Coprime {
  vector<T> bs;
  void add(T a) {
    assert(a >= 1);
    vector<T> bbs;
    for (const T b : bs) {
      vector<T> cs{a, b};
      for (int i = 1; i < static_cast<int>(cs.size()); ++i) {
        // invariant: cs[0, i): coprime
        for (int j = 0; j < i; ++j) {
          for (; cs[j] > 1 && cs[i] > 1; ) {
            if (cs[j] % cs[i] == 0) {
              cs[j] /= cs[i];
            } else if (cs[i] % cs[j] == 0) {
              cs[i] /= cs[j];
            } else {
              const T g = std::__gcd(cs[j], cs[i]);
              if (g > 1) {
                cs[j] /= g;
                cs[i] /= g;
                cs.push_back(g);
              }
              break;
            }
          }
        }
      }
      a = cs[0];
      for (int i = 1; i < static_cast<int>(cs.size()); ++i) {
        if (cs[i] > 1) bbs.push_back(cs[i]);
      }
    }
    if (a > 1) bbs.push_back(a);
    bs.swap(bbs);
  }
  vector<int> factorize(T a) const {
    assert(a >= 1);
    vector<int> es(bs.size(), 0);
    for (int i = 0; i < static_cast<int>(bs.size()); ++i) {
      for (; a % bs[i] == 0; a /= bs[i]) ++es[i];
    }
    assert(a == 1);
    return es;
  }
};  // Coprime

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <iostream>
#include <utility>

using std::cerr;
using std::endl;
using std::pair;

void unittest() {
  const long long as[3] = {
    1LL * 2*2 * 3*3 * 5*5 * 7*7 * 11 * 13 * 17 * 19,
    1LL * 2*2 * 3*3 * 5 * 7 * 11*11 * 13*13 * 17 * 19,
    1LL * 2*2 * 3 * 5*5 * 7 * 11*11 * 13 * 17*17 * 19,
  };
  Coprime<long long> c;
  assert(c.bs == (vector<long long>{}));
  assert(c.factorize(1) == (vector<int>{}));
  c.add(as[0]);
  assert(c.bs == (vector<long long>{as[0]}));
  assert(c.factorize(1) == (vector<int>{0}));
  assert(c.factorize(as[0]) == (vector<int>{1}));
  c.add(as[1]);
  assert(c.bs == (vector<long long>{5 * 7, 2*2 * 3*3 * 17 * 19, 11 * 13}));
  assert(c.factorize(1) == (vector<int>{0, 0, 0}));
  assert(c.factorize(as[0]) == (vector<int>{2, 1, 1}));
  assert(c.factorize(as[1]) == (vector<int>{1, 1, 2}));
  c.add(as[2]);
  assert(c.bs == (vector<long long>{7, 5, 3, 2*2 * 19, 17, 13, 11}));
  assert(c.factorize(1) == (vector<int>{0, 0, 0, 0, 0, 0, 0}));
  assert(c.factorize(as[0]) == (vector<int>{2, 2, 2, 1, 1, 1, 1}));
  assert(c.factorize(as[1]) == (vector<int>{1, 1, 2, 1, 1, 2, 2}));
  assert(c.factorize(as[2]) == (vector<int>{1, 2, 1, 1, 2, 1, 2}));
}

// https://atcoder.jp/contests/arc122/tasks/arc122_e
void arc122_e() {
  int N;
  for (; ~scanf("%d", &N); ) {
    vector<long long> A(N);
    for (int i = 0; i < N; ++i) scanf("%lld", &A[i]);
    Coprime<long long> c;
    for (int i = 0; i < N; ++i) c.add(A[i]);
    const int len = c.bs.size();
    vector<vector<int>> E(N);
    for (int i = 0; i < N; ++i) E[i] = c.factorize(A[i]);
    vector<int> used(N, 0);
    vector<int> ans;
    for (; ; ) {
      vector<pair<int, int>> mxs(len, std::make_pair(0, -1));
      for (int i = 0; i < N; ++i) if (!used[i]) {
        for (int k = 0; k < len; ++k) {
          if (mxs[k].first < E[i][k]) mxs[k] = std::make_pair(E[i][k], -1);
          if (mxs[k].first == E[i][k]) mxs[k].second = (~mxs[k].second) ? -2 : i;
        }
      }
      bool upd = false;
      for (int k = 0; k < len; ++k) {
        const int i = mxs[k].second;
        if (i >= 0 && !used[i]) {
          upd = true;
          used[i] = 1;
          ans.push_back(i);
        }
      }
      if (!upd) break;
    }
    if (static_cast<int>(ans.size()) == N) {
      puts("Yes");
      for (int h = N; --h >= 0; ) {
        printf("%lld", A[ans[h]]);
        if (h) printf(" ");
      }
      puts("");
    } else {
      puts("No");
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // arc122_e();
  return 0;
}
