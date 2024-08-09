#include <assert.h>
#include <algorithm>
#include <utility>
#include <vector>

using std::min;
using std::pair;
using std::vector;

// as, bs, cs: permutation of [0, n)
// A, B, C: unit monge matrix indexed by [0, n] * [0, n]
// A[i][j] = \sum[i<=i'<n] [as[i] < j]
//   as = [2, 0, 1, 3]
//   0 1 2 3 4
//        #   
//   0 1 2 2 3
//    #       
//   0 0 1 1 2
//      #     
//   0 0 0 0 1
//          # 
//   0 0 0 0 0
// C[i][j] = \min[0<=k<=n] (A[i][k] + B[k][j])
// O(n log(n)) time, O(n) space
vector<int> unitMongeMul(const vector<int> &as, const vector<int> &bs) {
  assert(as.size() == bs.size());
  const int n = as.size();
  int segN;
  for (segN = 1; segN < n; segN <<= 1) {}

  // suffix add, get rightmost min
  vector<int> mnA(segN << 1, 0), lzA(segN << 1, 0);
  auto addA = [&](int i, int val) -> void {
    if (i == segN) return;
    int ii = i += segN;
    for (int j = segN << 1; i < j; i >>= 1, j >>= 1, ii >>= 1) {
      if (i != ii) mnA[ii] = lzA[ii] + min(mnA[ii << 1], mnA[ii << 1 | 1]);
      if (i & 1) { mnA[i] += val; lzA[i] += val; ++i; }
    }
    for (; ii; ii >>= 1) mnA[ii] = lzA[ii] + min(mnA[ii << 1], mnA[ii << 1 | 1]);
  };
  auto getA = [&]() -> int {
    for (int a = 1; ; ) {
      if (a >= segN) return a - segN;
      a = (mnA[a << 1] < mnA[a << 1 | 1]) ? (a << 1) : (a << 1 | 1);
    }
  };

  // point erase, get suffix min
  vector<pair<int, int>> mnB(segN << 1, std::make_pair(n, -1));
  for (int i = 0; i < n; ++i) mnB[segN + i] = std::make_pair(bs[i], i);
  for (int a = segN; --a; ) mnB[a] = min(mnB[a << 1], mnB[a << 1 | 1]);
  auto eraseB = [&](int a) -> void {
    mnB[a += segN] = std::make_pair(n, -1);
    for (; a >>= 1; ) mnB[a] = min(mnB[a << 1], mnB[a << 1 | 1]);
  };
  auto getB = [&](int a) -> pair<int, int> {
    pair<int, int> ret(n, -1);
    a += segN;
    for (int b = segN << 1; a < b; a >>= 1, b >>= 1) {
      if (a & 1) ret = min(ret, mnB[a++]);
    }
    return ret;
  };

  vector<int> cs(n);
  for (int i = n; --i >= 0; ) {
    addA(as[i] + 1, +1);
    const auto res = getB(getA());
    cs[i] = res.first;
    addA(res.second + 1, -1);
    eraseB(res.second);
  }
  return cs;
}

vector<vector<int>> unitMongeMatrix(const vector<int> &as) {
  const int n = as.size();
  vector<vector<int>> A(n + 1, vector<int>(n + 1, 0));
  for (int i = n; --i >= 0; ) {
    for (int j = 0; j <= as[i]; ++j) A[i][j] = A[i + 1][j];
    for (int j = as[i] + 1; j <= n; ++j) A[i][j] = 1 + A[i + 1][j];
  }
  return A;
}

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <random>

using std::cerr;
using std::endl;
using std::mt19937_64;
using std::swap;

void unittest() {
  assert(unitMongeMul({2, 0, 1, 3}, {1, 0, 3, 2}) == (vector<int>{3, 1, 0, 2}));
  assert(unitMongeMatrix({2, 0, 1, 3}) == (vector<vector<int>>{
    {0, 1, 2, 3, 4},
    {0, 1, 2, 2, 3},
    {0, 0, 1, 1, 2},
    {0, 0, 0, 0, 1},
    {0, 0, 0, 0, 0},
  }));
  for (int n = 0; n <= 6; ++n) {
    vector<int> as(n);
    for (int i = 0; i < n; ++i) as[i] = i;
    do {
      vector<int> bs(n);
      for (int i = 0; i < n; ++i) bs[i] = i;
      do {
        const vector<int> cs = unitMongeMul(as, bs);
        const vector<vector<int>> A = unitMongeMatrix(as);
        const vector<vector<int>> B = unitMongeMatrix(bs);
        vector<vector<int>> C(n + 1, vector<int>(n + 1, n + 1));
        for (int i = 0; i <= n; ++i) for (int k = 0; k <= n; ++k) for (int j = 0; j <= n; ++j) {
          if (C[i][j] > A[i][k] + B[k][j]) {
            C[i][j] = A[i][k] + B[k][j];
          }
        }
        assert(C == unitMongeMatrix(cs));
      } while (next_permutation(bs.begin(), bs.end()));
    } while (next_permutation(as.begin(), as.end()));
  }
  mt19937_64 rng;
  for (int n = 7; n <= 100; ++n) {
    vector<int> as(n), bs(n);
    for (int i = 0; i < n; ++i) swap(as[rng() % (i + 1)], as[i] = i);
    for (int i = 0; i < n; ++i) swap(bs[rng() % (i + 1)], bs[i] = i);
    const vector<int> cs = unitMongeMul(as, bs);
    const vector<vector<int>> A = unitMongeMatrix(as);
    const vector<vector<int>> B = unitMongeMatrix(bs);
    vector<vector<int>> C(n + 1, vector<int>(n + 1, n + 1));
    for (int i = 0; i <= n; ++i) for (int k = 0; k <= n; ++k) for (int j = 0; j <= n; ++j) {
      if (C[i][j] > A[i][k] + B[k][j]) {
        C[i][j] = A[i][k] + B[k][j];
      }
    }
    assert(C == unitMongeMatrix(cs));
  }
}

void loj184() {
  int N;
  for (; ~scanf("%d", &N); ) {
    vector<int> as(N), bs(N);
    for (int i = 0; i < N; ++i) { scanf("%d", &as[i]); --as[i]; }
    for (int i = 0; i < N; ++i) { scanf("%d", &bs[i]); --bs[i]; }
    const vector<int> cs = unitMongeMul(as, bs);
    for (int i = 0; i < N; ++i) {
      if (i) printf(" ");
      printf("%d", cs[i] + 1);
    }
    puts("");
  }
}

int main() {
  // unittest(); cerr << "PASSED unittest" << endl;
  loj184();
  return 0;
}
