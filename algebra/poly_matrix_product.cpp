#include <assert.h>
#include <string.h>
#include <algorithm>
#include <initializer_list>
#include <iostream>
#include <vector>

using std::max;
using std::min;
using std::vector;

// TODO: refactor
// fft, invFft, inv, fac, invFac, Poly
#include "poly_998244353_portable.cpp"

// a(xL) ... a(xR-1)
//   a: d * d matrix of poly entry of size <= e
//   O(d^2 e^2 + d^2 sqrt(e (xR-xL)) log(e (xR-xL)) + d^3 sqrt(e (xR-xL))) time
//   Needs inv, fac, invFac for [0, e block), where
//     block: min power of 2 s.t. e block^2 >= xR-xL
vector<vector<Mint>> polyMatrixProduct(const vector<vector<Poly>> &a,
                                       long long xL, long long xR) {
  const int d = a.size();
  for (int i = 0; i < d; ++i) assert(static_cast<size_t>(d) == a[i].size());
  assert(xL <= xR);
  int e = 1;
  for (int i = 0; i < d; ++i) for (int j = 0; j < d; ++j) {
    for (; e < a[i][j].deg() + 1; e <<= 1) {}
  }
  long long block = 1;
  for (; e * block * block < xR - xL; block <<= 1) {}
  assert(e * block <= LIM_INV);
  const Mint invBlock = Mint(block).inv();
  // O(d^2 e^2) (more precisely, O(e \sum[i,j] a[i][j].size()))
  vector<Mint> b(d * d * e, 0);
  for (int i = 0; i < d; ++i) for (int j = 0; j < d; ++j) {
    for (int l = 0; l < e; ++l) {
      const Mint x = xL + block * l;
      Mint &y = b[(i * d + j) * e + l];
      for (int m = a[i][j].size(); --m >= 0; ) (y *= x) += a[i][j][m];
    }
  }
  // O(d^2 e block log(e block) + d^3 e block)
  for (int w = 1; w < block; w <<= 1) {
    // b[i][j]: product of w factors,
    //   evaluated at (xL, xL + block, ..., xL + block (ew-1))
    // for f: poly of size ew, given [f(0), ..., f(ew-1)], find:
    //   - [f(ew), ..., f(2ew-1)]
    //   - [f(w/block), ..., f(2ew-1+w/block)]
    const int ew = e * w;
    const int ew1 = ew << 1, ew2 = ew << 2;
    vector<Mint> workExp0(ew1, 0), workExp1(ew2, 0);
    vector<Mint> workInvExp0(ew1, 0);
    vector<Mint> workFall0(ew1, 0), workFall1(ew1, 0);
    for (int l = 0; l < ew; ++l) workExp0[l] = invFac[l];
    for (int l = 0; l < ew1; ++l) workExp1[l] = invFac[l];
    for (int l = 0; l < ew; ++l) workInvExp0[l] = (l & 1) ? -invFac[l] : invFac[l];
    workFall0[ew - 1] = workFall1[ew - 1] = 1;
    for (int l = 1; l < ew; ++l) workFall0[ew - 1 - l] = workFall0[ew - l] * (ew - (l - 1)) * inv[l];
    for (int l = 1; l < ew; ++l) workFall1[ew - 1 - l] = workFall1[ew - l] * (invBlock * w - (l - 1)) * inv[l];
    fft(workExp0);
    fft(workExp1);
    fft(workInvExp0);
    fft(workFall0);
    fft(workFall1);
    vector<Mint> b0(d * d * ew), b1(d * d * ew1);
    for (int i = 0; i < d; ++i) for (int j = 0; j < d; ++j) {
      const Mint *bij = b.data() + (i * d + j) * ew;
      Mint *b0ij = b0.data() + (i * d + j) * ew;
      Mint *b1ij = b1.data() + (i * d + j) * ew1;
      vector<Mint> ys0(ew1);
      for (int l = 0; l < ew; ++l) ys0[l] = invFac[l] * bij[l];
      fft(ys0);
      for (int l = 0; l < ew1; ++l) ys0[l] *= workInvExp0[l];
      invFft(ys0);
      for (int l = 0; l < ew1; ++l) ys0[l] *= fac[l];
      memset(ys0.data() + ew, 0, ew * sizeof(Mint));
      fft(ys0);
      vector<Mint> ys1 = ys0;
      for (int l = 0; l < ew1; ++l) ys0[l] *= workFall0[l];
      for (int l = 0; l < ew1; ++l) ys1[l] *= workFall1[l];
      invFft(ys0);
      invFft(ys1);
      ys0.erase(ys0.begin(), ys0.begin() + (ew - 1));
      ys1.erase(ys1.begin(), ys1.begin() + (ew - 1));
      for (int l = 0; l < ew; ++l) ys0[l] *= invFac[l];
      for (int l = 0; l < ew; ++l) ys1[l] *= invFac[l];
      ys0.resize(ew1, 0);
      ys1.resize(ew2, 0);
      fft(ys0);
      fft(ys1);
      for (int l = 0; l < ew1; ++l) ys0[l] *= workExp0[l];
      for (int l = 0; l < ew2; ++l) ys1[l] *= workExp1[l];
      invFft(ys0);
      invFft(ys1);
      for (int l = 0; l < ew; ++l) b0ij[l] = fac[l] * ys0[l];
      for (int l = 0; l < ew1; ++l) b1ij[l] = fac[l] * ys1[l];
    }
    vector<Mint> bb(d * d * ew1, 0);
    for (int i = 0; i < d; ++i) for (int k = 0; k < d; ++k) for (int j = 0; j < d; ++j) {
      Mint *bbij = bb.data() + ((i * d + j) * ew1);
      const Mint *bik = b.data() + ((i * d + k) * ew);
      const Mint *b0ik = b0.data() + ((i * d + k) * ew);
      const Mint *b1kj = b1.data() + ((k * d + j) * ew1);
      for (int l = 0; l < ew; ++l) bbij[l] += bik[l] * b1kj[l];
      for (int l = 0; l < ew; ++l) bbij[ew + l] += b0ik[l] * b1kj[ew + l];
    }
    b = bb;
  }
  vector<Mint> c(d * d, 0);
  for (int i = 0; i < d; ++i) c[i * d + i] = 1;
  long long x = xL;
  // O(d^3 (xR-xL)/block) <= O(d^3 e block)
  for (int l = 0; x + block <= xR; ++l, x += block) {
    vector<Mint> cc(d * d, 0);
    for (int i = 0; i < d; ++i) for (int k = 0; k < d; ++k) for (int j = 0; j < d; ++j) {
      cc[i * d + j] += c[i * d + k] * b[(k * d + j) * e * block + l];
    }
    c = cc;
  }
  // O(d^3 block + d^2 e block)
  for (; x < xR; ++x) {
    const Mint x_ = x;
    vector<Mint> ax(d * d, 0), cc(d * d, 0);
    for (int i = 0; i < d; ++i) for (int j = 0; j < d; ++j) {
      Mint &y = ax[i * d + j];
      for (int m = a[i][j].size(); --m >= 0; ) (y *= x_) += a[i][j][m];
    }
    for (int i = 0; i < d; ++i) for (int k = 0; k < d; ++k) for (int j = 0; j < d; ++j) {
      cc[i * d + j] += c[i * d + k] * ax[k * d + j];
    }
    c = cc;
  }
  vector<vector<Mint>> ret(d, vector<Mint>(d));
  for (int i = 0; i < d; ++i) for (int j = 0; j < d; ++j) ret[i][j] = c[i * d + j];
  return ret;
}

////////////////////////////////////////////////////////////////////////////////

using std::cerr;
using std::endl;

void unittest() {
  using Int = long long;
  {
    const vector<vector<Poly>> a;
    auto test = [&](Int xL, Int xR) -> void {
      assert(polyMatrixProduct(a, xL, xR).empty());
    };
    test(0, 0);
    test(3, 13);
    test(1'000'000'000, 2'000'000'000);
  }
  {
    const vector<vector<Poly>> a{
      {{2}}
    };
    auto test = [&](Int xL, Int xR) -> void {
      assert(polyMatrixProduct(a, xL, xR) == (vector<vector<Mint>>{
        {Mint(2).pow(xR - xL)}
      }));
    };
    test(0, 0);
    test(3, 13);
    test(1'000'000'000, 2'000'000'000);
  }
  {
    const vector<vector<Poly>> a{
      {{0, 1}}
    };
    auto test = [&](Int xL, Int xR) -> void {
      assert(polyMatrixProduct(a, xL, xR) == (vector<vector<Mint>>{
        {(xL == xR) ? 1 : (xL == 0) ? 0 : (invFac[xL - 1] * fac[xR - 1])}
      }));
    };
    test(0, 0);
    test(0, 10);
    test(1, 6);
    test(1, 10);
    test(3, 13);
    test(1234, 5678);
    test(12345, 654321);
    assert(polyMatrixProduct(a, 1, MO) == (vector<vector<Mint>>{
      {-1}
    }));
    assert(polyMatrixProduct(a, 1, MO + 1) == (vector<vector<Mint>>{
      {0}
    }));
  }
  {
    const vector<vector<Poly>> a{
      {{0, 0, 1}}
    };
    auto test = [&](Int xL, Int xR) -> void {
      assert(polyMatrixProduct(a, xL, xR) == (vector<vector<Mint>>{
        {(xL == xR) ? 1 : (xL == 0) ? 0 : (invFac[xL - 1] * fac[xR - 1]).pow(2)}
      }));
    };
    test(0, 0);
    test(0, 10);
    test(1, 6);
    test(1, 10);
    test(3, 13);
    test(1234, 5678);
    test(12345, 654321);
    assert(polyMatrixProduct(a, 1, MO) == (vector<vector<Mint>>{
      {1}
    }));
    assert(polyMatrixProduct(a, 1, MO + 1) == (vector<vector<Mint>>{
      {0}
    }));
  }
  {
    const int d = 3, e = 5;
    const vector<vector<Poly>> a{
      {{3, 1, 4, 1, 5}, {9, 2, 6, 5, 3}, {5, 8, 9, 7, 9}},
      {{3, 2, 3, 8, 4}, {6, 2, 6, 4, 3}, {3, 8, 3, 2, 7}},
      {{9, 5, 0, 2, 8}, {8, 4, 1, 9, 7}, {1, 6, 9, 3, 9}},
    };
    for (const Int xL : vector<Int>{
      -999'999'999'999LL, -12345, -6789, -1,
      0, 1, 1357, 24680, 1'000'000'007'998'244'353LL,
    }) {
      vector<vector<Mint>> c(d, vector<Mint>(d, 0));
      for (int i = 0; i < d; ++i) c[i][i] = 1;
      for (Int x = xL; x <= xL + 10'000; ++x) {
        assert(polyMatrixProduct(a, xL, x) == c);
        vector<vector<Mint>> ax(d, vector<Mint>(d, 0));
        for (int i = 0; i < d; ++i) for (int j = 0; j < d; ++j) {
          Mint pw = 1;
          for (int h = 0; h < e; ++h) {
            ax[i][j] += a[i][j][h] * pw;
            pw *= x;
          }
        }
        vector<vector<Mint>> cc(d, vector<Mint>(d, 0));
        for (int i = 0; i < d; ++i) for (int j = 0; j < d; ++j) for (int k = 0; k < d; ++k) {
          cc[i][j] += c[i][k] * ax[k][j];
        }
        c = cc;
      }
    }
  }
  // https://yukicoder.me/problems/no/2166
  // K! [x^K] (1 + 2 x + (1/2) x^2)^N
  {
    auto test = [&](Int N, Int K, Mint expected) -> void {
      const vector<vector<Poly>> a{
        {{2 * (N + 1), -2}, {1}},
        {{-N - 1, N + Mint(3) / 2, -Mint(1) / 2}, {}},
      };
      assert(polyMatrixProduct(a, 1, K + 1)[0][0] == expected);
    };
    test(1, 0, 1);
    test(1, 1, 2);
    test(1, 2, 1);
    test(2, 0, 1);
    test(2, 1, 4);
    test(2, 2, 10);
    test(2, 3, 12);
    test(2, 4, 6);
    test(3, 0, 1);
    test(3, 1, 6);
    test(3, 2, 27);
    test(3, 3, 84);
    test(3, 4, 162);
    test(3, 5, 180);
    test(3, 6, 90);
    test(12345, 6789, 200042644);
    test(20221218, 100000, 306869647);
    test(1000000000000000000LL, 987654321, 629032458);
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
