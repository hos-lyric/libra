#include <algorithm>
#include <vector>

using std::max;
using std::vector;

// "a[i][j0] -> a[i][j1]" means a[i][j1] is better
// a: totally monotone <=> for i0 < i1:
//   a[i0][j0] -> a[i0][j1] ==> a[i1][j0] -> a[i1][j1]
//   a[i0][j0] <- a[i0][j1] <== a[i1][j0] <- a[i1][j1]
// cmp(i, j0, j1): "a[i][j0] -> a[i][j1]"
//   called only for j0 < j1
//   for a[i][j0] = a[i][j1]:
//     false to prefer smaller index
//     true to prefer larger index

namespace smawk_impl {
constexpr int MAX_M = 1 << 20;
constexpr int MAX_N = 1 << 20;
int is0[2 * MAX_M], js0[max(2 * MAX_M, MAX_N)];
template <class Cmp> struct Smawk {
  const int m, n;
  const Cmp cmp;
  vector<int> jms;
  Smawk(int m_, int n_, Cmp cmp_) : m(m_), n(n_), cmp(cmp_) {
    for (int i = 0; i < m; ++i) is0[i] = i;
    for (int j = 0; j < n; ++j) js0[j] = j;
    jms.assign(m, -1);
    rec(is0, m, js0, n);
  }
  void rec(int *is, int isLen, int *js, int jsLen) {
    if (!isLen || !jsLen) return;
    if (isLen < jsLen) {
      int len = 0;
      for (int y = 0; y < jsLen; ++y) {
        const int j = js[y];
        for (; len && cmp(is[len - 1], js[len - 1], j); --len) {}
        if (len != isLen) js[len++] = j;
      }
      jsLen = len;
    }
    int *iis = is + isLen, *jjs = js + jsLen;
    int iisLen = 0;
    for (int x = 1; x < isLen; x += 2) iis[iisLen++] = is[x];
    for (int y = 0; y < jsLen; ++y) jjs[y] = js[y];
    rec(iis, iisLen, jjs, jsLen);
    for (int x = 0, y = 0; x < isLen; x += 2) {
      const int i = is[x];
      const int j1 = (x + 1 < isLen) ? jms[is[x + 1]] : js[jsLen - 1];
      for (; ; ) {
        const int j = js[y];
        if (!~jms[i] || cmp(i, jms[i], j)) jms[i] = j;
        if (j == j1) break;
        ++y;
      }
    }
  }
};
}  // smawk_impl
template <class Cmp> vector<int> smawk(int m, int n, Cmp cmp) {
  return smawk_impl::Smawk<Cmp>(m, n, cmp).jms;
}

// cs[k] = \min[i+j=k] (as[i] + bs[j])
// as: convex
template <class T>
vector<T> minPlusConvolveConvex(const vector<T> as, const vector<T> &bs) {
  const int asLen = as.size(), bsLen = bs.size();
  if (!asLen || !bsLen) return {};
  const auto jms = smawk(asLen + bsLen - 1, bsLen, [&](int i, int j0, int j1) -> bool {
    if (i - j0 >= asLen) return true;
    if (i - j1 < 0) return false;
    return (as[i - j0] + bs[j0] > as[i - j1] + bs[j1]);
  });
  vector<T> cs(asLen + bsLen - 1);
  for (int i = 0; i < asLen + bsLen - 1; ++i) cs[i] = as[i - jms[i]] + bs[jms[i]];
  return cs;
}

// cs[k] = \min[i+j=k] (as[i] + bs[j])
// as: concave
template <class T>
vector<T> maxPlusConvolveConcave(const vector<T> as, const vector<T> &bs) {
  const int asLen = as.size(), bsLen = bs.size();
  if (!asLen || !bsLen) return {};
  const auto jms = smawk(asLen + bsLen - 1, bsLen, [&](int i, int j0, int j1) -> bool {
    if (i - j0 >= asLen) return true;
    if (i - j1 < 0) return false;
    return (as[i - j0] + bs[j0] < as[i - j1] + bs[j1]);
  });
  vector<T> cs(asLen + bsLen - 1);
  for (int i = 0; i < asLen + bsLen - 1; ++i) cs[i] = as[i - jms[i]] + bs[jms[i]];
  return cs;
}

////////////////////////////////////////////////////////////////////////////////

#include <assert.h>
#include <stdio.h>
#include <chrono>
#include <iostream>
#include <random>
#include <set>
#include <utility>

using std::cerr;
using std::endl;
using std::pair;
using std::set;
using std::mt19937_64;

// maxima
int counterSmall;
void checkSmall(int m, int n, const vector<vector<int>> &a) {
  ++counterSmall;
  const vector<int> jms = smawk(m, n, [&](int i, int j0, int j1) -> bool {
    assert(0 <= i); assert(i < m);
    assert(0 <= j0); assert(j0 < j1); assert(j1 < n);
    return (a[i][j0] < a[i][j1]);
  });
  for (int i = 0; i < m; ++i) {
    int jm = -1;
    for (int j = 0; j < n; ++j) if (!~jm || a[i][jm] < a[i][j]) jm = j;
    assert(jms[i] == jm);
  }
}
void dfsSmall(int m, int n, int x, int y, vector<vector<int>> &a) {
  if (y == n) {
    checkSmall(x + 1, n, a);
    if (x + 1 < m) {
      dfsSmall(m, n, x + 1, 0, a);
    }
  } else {
    for (a[x][y] = 0; a[x][y] < n; ++a[x][y]) {
      if ([&]() -> bool {
        if (x > 0) {
          for (int yy = 0; yy < y; ++yy) {
            if (a[x - 1][yy] < a[x - 1][y] && a[x][yy] >= a[x][y]) return false;
            if (a[x - 1][yy] <= a[x - 1][y] && a[x][yy] > a[x][y]) return false;
          }
        }
        return true;
      }()) {
        dfsSmall(m, n, x, y + 1, a);
      }
    }
  }
}

void unittest() {
  for (int m = 0; m <= 4; ++m) for (int n = 1; n <= 4; ++n) {
    // false to prefer smaller index
    // true to prefer larger index
    assert(smawk(m, n, [&](int, int, int) -> bool { return false; }) == vector<int>(m, 0));
    assert(smawk(m, n, [&](int, int, int) -> bool { return true; }) == vector<int>(m, n - 1));
  }
  {
    // minima
    // http://web.cs.unlv.edu/larmore/Courses/CSC477/monge.pdf
    const vector<vector<int>> a{
      {25, 21, 13, 10, 20, 13, 19, 35, 37, 41, 58, 66, 82, 99, 124, 133, 156, 178},
      {42, 35, 26, 20, 29, 21, 25, 37, 36, 39, 56, 64, 76, 91, 116, 125, 146, 164},
      {57, 48, 35, 28, 33, 24, 28, 40, 37, 37, 54, 61, 72, 83, 107, 113, 131, 146},
      {78, 65, 51, 42, 44, 35, 38, 48, 42, 42, 55, 61, 70, 80, 100, 106, 120, 135},
      {90, 76, 58, 48, 49, 39, 42, 48, 39, 35, 47, 51, 56, 63, 80, 86, 97, 110},
      {103, 85, 67, 56, 55, 44, 44, 49, 39, 33, 41, 44, 49, 56, 71, 75, 84, 96},
      {123, 105, 86, 75, 73, 59, 57, 62, 51, 44, 50, 52, 55, 59, 72, 74, 80, 92},
      {142, 123, 100, 86, 82, 65, 61, 62, 50, 43, 47, 45, 46, 46, 58, 59, 65, 73},
      {151, 130, 104, 88, 80, 59, 52, 49, 37, 29, 29, 24, 23, 20, 28, 25, 31, 39},
    };
    const int m = a.size(), n = a[0].size();
    vector<vector<int>> asked(m, vector<int>(n, 0));
    assert(smawk(m, n, [&](int i, int j0, int j1) -> bool {
      assert(0 <= i); assert(i < m);
      assert(0 <= j0); assert(j0 < j1); assert(j1 < n);
      return (a[i][j0] > a[i][j1]);
    }) == (vector<int>{3, 3, 5, 5, 9, 9, 9, 9, 13}));
  }
  {
    const int ms[7 + 1] = {0, 7, 6, 5, 4, 3, 2, 1};
    for (int n = 1; n <= 7; ++n) {
      counterSmall = 0;
      vector<vector<int>> a(ms[n], vector<int>(n));
      dfsSmall(ms[n], n, 0, 0, a);
      cerr << "n = " << n << ": counterSmall = " << counterSmall << endl;
    }
  }
  for (int m = 1; m <= 1'000'000; m *= 100) {
    for (int n = 1; n <= 1'000'000; n *= 100) {
      // 1-dim nearest
      mt19937_64 rng;
      vector<int> ps(m), qs(n);
      for (int i = 0; i < m; ++i) ps[i] = rng() >> 33;
      for (int j = 0; j < n; ++j) qs[j] = rng() >> 33;
      std::sort(ps.begin(), ps.end());
      std::sort(qs.begin(), qs.end());
      {
        int numCalls = 0;
        set<pair<int, int>> asked;
        const vector<int> jms = smawk(m, n, [&](int i, int j0, int j1) -> bool {
          ++numCalls;
          asked.emplace(i, j0);
          asked.emplace(i, j1);
          return (abs(qs[j0] - ps[i]) > abs(qs[j1] - ps[i]));
        });
        cerr << "m = " << m << ", n = " << n << ": "
             << "numCalls = " << numCalls << ", |asked| = " << asked.size() << endl;
      }
      {
        const auto timerBegin = std::chrono::high_resolution_clock::now();
        const vector<int> jms = smawk(m, n, [&](int i, int j0, int j1) -> bool {
          return (abs(qs[j0] - ps[i]) > abs(qs[j1] - ps[i]));
        });
        const auto timerEnd = std::chrono::high_resolution_clock::now();
        cerr << "m = " << m << ", n = " << n << ": "
             << std::chrono::duration_cast<std::chrono::milliseconds>(
                 timerEnd - timerBegin).count() << " msec" << endl;
      }
    }
  }
  {
    assert(minPlusConvolveConvex(vector<int>{}, vector<int>{}).empty());
    assert(minPlusConvolveConvex(vector<int>{}, vector<int>{2}).empty());
    assert(minPlusConvolveConvex(vector<int>{2}, vector<int>{}).empty());
    assert(maxPlusConvolveConcave(vector<int>{}, vector<int>{}).empty());
    assert(maxPlusConvolveConcave(vector<int>{}, vector<int>{2}).empty());
    assert(maxPlusConvolveConcave(vector<int>{2}, vector<int>{}).empty());
  }
  {
    constexpr long long INF = 1'000'000'000'000'000'000LL;
    constexpr long long LIM = 1'000'000'000'000LL;
    mt19937_64 rng;
    for (const int m : {1, 10, 100}) for (const int n : {1, 10, 100}) {
      vector<long long> slopes(m - 1);
      for (int i = 0; i < m - 1; ++i) slopes[i] = -LIM + rng() % (2 * LIM + 1);
      std::sort(slopes.begin(), slopes.end());
      vector<long long> as(m), bs(n);
      as[0] = -LIM + rng() % (2 * LIM + 1);
      for (int i = 0; i < m - 1; ++i) as[i + 1] = as[i] + slopes[i];
      for (int j = 0; j < n; ++j) bs[j] = -LIM + rng() % (2 * LIM + 1);
      vector<long long> expected(m + n - 1, INF);
      for (int i = 0; i < m; ++i) for (int j = 0; j < n; ++j) {
        if (expected[i + j] > as[i] + bs[j]) expected[i + j] = as[i] + bs[j];
      }
      const vector<long long> actual = minPlusConvolveConvex(as, bs);
      assert(expected == actual);
    }
    for (const int m : {1, 10, 100}) for (const int n : {1, 10, 100}) {
      vector<long long> slopes(m - 1);
      for (int i = 0; i < m - 1; ++i) slopes[i] = -LIM + rng() % (2 * LIM + 1);
      std::sort(slopes.begin(), slopes.end(), std::greater<long long>());
      vector<long long> as(m), bs(n);
      as[0] = -LIM + rng() % (2 * LIM + 1);
      for (int i = 0; i < m - 1; ++i) as[i + 1] = as[i] + slopes[i];
      for (int j = 0; j < n; ++j) bs[j] = -LIM + rng() % (2 * LIM + 1);
      vector<long long> expected(m + n - 1, -INF);
      for (int i = 0; i < m; ++i) for (int j = 0; j < n; ++j) {
        if (expected[i + j] < as[i] + bs[j]) expected[i + j] = as[i] + bs[j];
      }
      const vector<long long> actual = maxPlusConvolveConcave(as, bs);
      assert(expected == actual);
    }
  }
}

// https://judge.yosupo.jp/problem/min_plus_convolution_convex_arbitrary
void yosupo_min_plus_convolution_convex_arbitrary() {
  int ALen, BLen;
  for (; ~scanf("%d%d", &ALen, &BLen); ) {
    vector<int> A(ALen), B(BLen);
    for (int i = 0; i < ALen; ++i) scanf("%d", &A[i]);
    for (int i = 0; i < BLen; ++i) scanf("%d", &B[i]);
    const vector<int> C = minPlusConvolveConvex(A, B);
    for (int i = 0; i < ALen + BLen - 1; ++i) {
      if (i) printf(" ");
      printf("%d", C[i]);
    }
    puts("");
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupo_min_plus_convolution_convex_arbitrary();
  return 0;
}
