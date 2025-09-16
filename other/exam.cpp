#include <assert.h>
#include <vector>

using std::vector;

// determine (x[0], ..., x[n-1]) \in {0,1}^n
// by linear system \sum[j] a[i][j] x[j] = b[i] with a[i][j] \in {-1,0,+1}
// A[0] = [ +1 ]
// A[d] = [ +A[d-1] +A[d-1] I ]
//        [ +A[d-1] -A[d-1] 0 ]
// size: (2^d) * (2^d (2+d)/2)
//   0 <= d <= 10: 1 3 8 20 48 112 256 576 1280 2816 6144
// columns permuted
// ++++++++ ++++ + +  +   
// +-+-+-+-       + +  +  
// ++--++-- +-+-        + 
// +--++--+              +
// ++++---- ++-- + -      
// +-+--+-+       + -     
// ++----++ +--+          
// +--+-++-               
struct SysSign {
  int d, m, n, nn;
  vector<vector<char>> a;
  static int maxN(int d) {
    return ((2 + d) << d) / 2;
  }
  SysSign() {}
  explicit SysSign(int n_) : n(n_) {
    for (d = 0; (nn = maxN(d)) < n; ++d) {}
    a.assign(m = 1<<d, vector<char>(nn, 0));
    for (int i = 0; i < m; ++i) {
      for (int p = 0; p < m; ++p) a[i][p] = __builtin_parity(i & p) ? -1 : +1;
      for (int e = 0; e < d; ++e) if (!(i >> e & 1)) {
        for (int p = 0; p < 1 << (d-1-e); ++p) {
          a[i][((2+e)<<(d-1)) + (p<<e) + (i&((1<<e)-1))] = __builtin_parity((i>>(e+1)) & p) ? -1 : +1;
        }
      }
    }
  }
  vector<int> solve(vector<int> bs) const {
    assert((int)bs.size() == m);
    vector<int> xs(nn, 0);
    for (int e = d; --e >= 0; ) {
      int j = (2+e)<<(d-1);
      for (int h = 0; h < m; h += (1<<(e+1))) for (int i0 = h; i0 < h + (1<<e); ++i0) {
        const int i1 = i0 + (1<<e);
        const int b0 = bs[i0], b1 = bs[i1];
        const int t = (b0 + b1) & 1;
        xs[j++] = t;
        bs[i0] = (b0 - t + b1) / 2;
        bs[i1] = (b0 - t - b1) / 2;
      }
    }
    for (int i = 0; i < m; ++i) xs[i] = bs[i];
    xs.resize(n);
    return xs;
  }
};

// determine (x[0], ..., x[n-1]) \in {0,1}^n
// by linear system \sum[j] a[i][j] x[j] = b[i] with a[i][j] \in {0,1}
// A[0] = [ 1 ]
// A[d] = [ A[d-1] S ]  where S - T: SysSign for d-1
//        [ A[d-1] T ]
// size: (2^d) * (1 + 2^d d/2)
//   0 <= d <= 10: 1 2 5 13 33 81 193 449 1025 2305 5121
// 1 1 111 1111111*
// 1 0 10* 1010***1
// 1 1 000 110010**
// 1 0 01* 1001****
// 1 1 111 0000000*
// 1 0 10* 0101***0
// 1 1 000 001101**
// 1 0 01* 0110****
// fill * with 1 so that a[0][j] = 1
// for 2-choice exam:
//   \sum[j] [x[j] = a[i][j]] = \sum[j] [a[i][j] = 0] - \sum[j] x[j] + 2 \sum[j] a[i][j] x[j]
struct Sys01 {
  int d, m, n, nn;
  vector<vector<char>> a;
  vector<int> pt;
  vector<SysSign> sysSigns;
  static int maxN(int d) {
    return 1 + (d << d) / 2;
  }
  Sys01() {}
  explicit Sys01(int n_) : n(n_) {
    for (d = 0; (nn = maxN(d)) < n; ++d) {}
    pt.resize(d + 1);
    sysSigns.resize(d + 1);
    pt[0] = 1;
    for (int e = 0; e < d; ++e) {
      sysSigns[e] = SysSign(((2+e)<<e)/2);
      pt[e + 1] = pt[e] + sysSigns[e].nn;
    }
    assert(pt[d] == nn);
    a.assign(m = 1<<d, vector<char>(nn, 0));
    for (int i = 0; i < m; ++i) {
      a[i][0] = 1;
      for (int e = 0; e < d; ++e) {
        const int ii = i & ((1<<e)-1);
        const int sig = (i >> e & 1) ? -1 : +1;
        for (int j = 0; j < sysSigns[e].nn; ++j) {
          // Replace >= 0 with > when we want a sparse matrix (solveExam fails).
          a[i][pt[e] + j] = (sig * sysSigns[e].a[ii][j] >= 0) ? 1 : 0;
        }
      }
    }
  }
  vector<int> solve(vector<int> bs) const {
    assert((int)bs.size() == m);
    vector<int> xs(nn);
    for (int e = d; --e >= 0; ) {
      vector<int> diffs(1<<e);
      for (int i = 0; i < 1<<e; ++i) diffs[i] = bs[i] - bs[i + (1<<e)];
      const auto ys = sysSigns[e].solve(diffs);
      for (int j = 0; j < sysSigns[e].nn; ++j) xs[pt[e] + j] = ys[j];
      for (int i = 0; i < 1<<e; ++i) {
        for (int j = 0; j < sysSigns[e].nn; ++j) bs[i] -= a[i][pt[e] + j] * ys[j];
      }
    }
    xs[0] = bs[0];
    xs.resize(n);
    return xs;
  }
  vector<int> solveExam(vector<int> bs) const {
    assert((int)bs.size() == m);
    assert(a[0] == vector<char>(nn, 1));
    for (int i = 1; i < m; ++i) {
      for (int j = 0; j < n; ++j) if (!a[i][j]) --bs[i];
      bs[i] += bs[0];
      assert(bs[i] % 2 == 0);
      bs[i] /= 2;
    }
    return solve(bs);
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>
#include <iostream>

using std::cerr;
using std::endl;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void unittest_SysSign() {
  cerr << "SysSign::maxN = ";
  for (int d = 0; d <= 10; ++d) cerr << SysSign::maxN(d) << " ";
  cerr << endl;
  assert(SysSign(0).d == 0);
  assert(SysSign(1).d == 0);
  assert(SysSign(2).d == 1);
  assert(SysSign(3).d == 1);
  assert(SysSign(4).d == 2);
  assert(SysSign(8).d == 2);
  assert(SysSign(9).d == 3);
  assert(SysSign(20).d == 3);
  assert(SysSign(21).d == 4);
  assert(SysSign(48).d == 4);
  assert(SysSign(49).d == 5);
  assert(SysSign(576).d == 7);
  assert(SysSign(577).d == 8);
  assert(SysSign(6144).d == 10);
  assert(SysSign(6145).d == 11);
  for (int n = 0; n <= 16; ++n) {
    const SysSign sys(n);
    assert(1 << sys.d == sys.m);
    assert(static_cast<int>(sys.a.size()) == sys.m);
    assert(n == sys.n);
    assert(n <= sys.nn);
    for (int i = 0; i < sys.m; ++i) {
      assert(static_cast<int>(sys.a[i].size()) == sys.nn);
      for (int j = 0; j < sys.nn; ++j) {
        assert(-1 <= sys.a[i][j]); assert(sys.a[i][j] <= +1);
      }
    }
    for (int p = 0; p < 1 << n; ++p) {
      vector<int> xs(n);
      for (int j = 0; j < n; ++j) xs[j] = p >> j & 1;
      vector<int> bs(sys.m, 0);
      for (int i = 0; i < sys.m; ++i) for (int j = 0; j < n; ++j) {
        bs[i] += static_cast<int>(sys.a[i][j]) * xs[j];
      }
      assert(xs == sys.solve(bs));
    }
  }
  for (int n = 0; n <= 100; ++n) {
    const SysSign sys(n);
    assert(1 << sys.d == sys.m);
    assert(static_cast<int>(sys.a.size()) == sys.m);
    assert(n == sys.n);
    assert(n <= sys.nn);
    for (int i = 0; i < sys.m; ++i) {
      assert(static_cast<int>(sys.a[i].size()) == sys.nn);
      for (int j = 0; j < sys.nn; ++j) {
        assert(-1 <= sys.a[i][j]); assert(sys.a[i][j] <= +1);
      }
    }
    vector<int> xs(n);
    for (int j = 0; j < n; ++j) xs[j] = xrand() & 1;
    vector<int> bs(sys.m, 0);
    for (int i = 0; i < sys.m; ++i) for (int j = 0; j < n; ++j) {
      bs[i] += static_cast<int>(sys.a[i][j]) * xs[j];
    }
    assert(xs == sys.solve(bs));
  }
}

void unittest_Sys01() {
  cerr << "Sys01::maxN = ";
  for (int d = 0; d <= 10; ++d) cerr << Sys01::maxN(d) << " ";
  cerr << endl;
  assert(Sys01(0).d == 0);
  assert(Sys01(1).d == 0);
  assert(Sys01(2).d == 1);
  assert(Sys01(3).d == 2);
  assert(Sys01(5).d == 2);
  assert(Sys01(6).d == 3);
  assert(Sys01(13).d == 3);
  assert(Sys01(14).d == 4);
  assert(Sys01(33).d == 4);
  assert(Sys01(34).d == 5);
  assert(Sys01(449).d == 7);
  assert(Sys01(450).d == 8);
  assert(Sys01(5121).d == 10);
  assert(Sys01(5122).d == 11);
  for (int n = 0; n <= 16; ++n) {
    const Sys01 sys(n);
    assert(1 << sys.d == sys.m);
    assert(static_cast<int>(sys.a.size()) == sys.m);
    assert(n == sys.n);
    assert(n <= sys.nn);
    for (int i = 0; i < sys.m; ++i) {
      assert(static_cast<int>(sys.a[i].size()) == sys.nn);
      for (int j = 0; j < sys.nn; ++j) {
        assert(0 <= sys.a[i][j]); assert(sys.a[i][j] <= +1);
      }
    }
    for (int p = 0; p < 1 << n; ++p) {
      vector<int> xs(n);
      for (int j = 0; j < n; ++j) xs[j] = p >> j & 1;
      vector<int> bs(sys.m, 0), cs(sys.m, 0);
      for (int i = 0; i < sys.m; ++i) for (int j = 0; j < n; ++j) {
        bs[i] += static_cast<int>(sys.a[i][j]) * xs[j];
        cs[i] += ((xs[j] == sys.a[i][j]) ? 1 : 0);
      }
      assert(xs == sys.solve(bs));
      assert(xs == sys.solveExam(cs));
    }
  }
  for (int n = 0; n <= 100; ++n) {
    const Sys01 sys(n);
    assert(1 << sys.d == sys.m);
    assert(static_cast<int>(sys.a.size()) == sys.m);
    assert(n == sys.n);
    assert(n <= sys.nn);
    for (int i = 0; i < sys.m; ++i) {
      assert(static_cast<int>(sys.a[i].size()) == sys.nn);
      for (int j = 0; j < sys.nn; ++j) {
        assert(0 <= sys.a[i][j]); assert(sys.a[i][j] <= +1);
      }
    }
    vector<int> xs(n);
    for (int j = 0; j < n; ++j) xs[j] = xrand() & 1;
    vector<int> bs(sys.m, 0), cs(sys.m, 0);
    for (int i = 0; i < sys.m; ++i) for (int j = 0; j < n; ++j) {
      bs[i] += static_cast<int>(sys.a[i][j]) * xs[j];
      cs[i] += ((xs[j] == sys.a[i][j]) ? 1 : 0);
    }
    assert(xs == sys.solve(bs));
    assert(xs == sys.solveExam(cs));
  }
}

// https://www.luogu.com.cn/problem/T183641
void luogu_T183641() {
  int N, LIM;
  scanf("%d%d", &N, &LIM);
  const Sys01 sys(N);
  assert(sys.m + 1 <= LIM);
  vector<int> bs(sys.m, 0);
  for (int i = 0; i < sys.m; ++i) {
    for (int j = 0; j < N; ++j) putchar("NY"[static_cast<int>(sys.a[i][j])]);
    puts("");
    fflush(stdout);
    scanf("%d", &bs[i]);
    if (bs[i] == N) exit(0);
  }
  const vector<int> xs = sys.solveExam(bs);
  for (int j = 0; j < N; ++j) putchar("NY"[xs[j]]);
  puts("");
  fflush(stdout);
  int b;
  scanf("%d", &b);
  assert(b == N);
}

int main() {
  unittest_SysSign(); cerr << "PASSED unittest_SysSign" << endl;
  unittest_Sys01(); cerr << "PASSED unittest_Sys01" << endl;
  // luogu_T183641();
  return 0;
}
