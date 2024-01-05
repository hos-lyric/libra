#include <assert.h>
#include <algorithm>
#include <utility>
#include <vector>

using std::pair;
using std::vector;

// add X^x Y^y (1-X)^-(a+1) (1-Y)^-(b+1)
// get [X^x Y^y]
// [X^x' Y^y'] X^x Y^y (1-X)^-(a+1) (1-Y)^-(b+1)
// = [x<=x'] [y<=y'] binom(x'-x+a,a) binom(y'-y+b,b)
// = [x<=x'] [y<=y'] (x'+1-x)^(rise a)/a! (y'+1-y)^(rise b)/b!
// = [x<=x'] [y<=y'] \sum[0<=a'<=a] \sum[0<=b'<=b] (x'+1)^(rise a')/a'! (-x)^(rise a-a')/(a-a')! (y'+1)^(rise b')/b'! (-y)^(rise b-b')/(b-b')!
template <class X, class Y, class T, int A, int B> struct StaticPrefixSumAdd {
  // x^(rise a)/a!, y^(rise b)/b!
  T xRise[A + 1], yRise[B + 1];
  void riseX(int a, X x) {
    static_assert(0 <= A); static_assert(A <= 4);
    assert(0 <= a); assert(a <= A);
    xRise[0] = 1;
    if (a == 0) return;
    X x0 = x;
    xRise[1] = T(x0);
    if (a == 1) return;
    X x1 = x + 1;
    ((x0 % 2 == 0) ? x0 : x1) /= 2;
    xRise[2] = T(x0) * T(x1);
    if (a == 2) return;
    X x2 = x + 2;
    ((x0 % 3 == 0) ? x0 : (x1 % 3 == 0) ? x1 : x2) /= 3;
    xRise[3] = T(x0) * T(x1) * T(x2);
    if (a == 3) return;
    X x3 = x + 3;
    ((x0 % 2 == 0) ? x0 : (x1 % 2 == 0) ? x1 : (x2 % 2 == 0) ? x2 : x3) /= 2;
    ((x0 % 2 == 0) ? x0 : (x1 % 2 == 0) ? x1 : (x2 % 2 == 0) ? x2 : x3) /= 2;
    xRise[4] = T(x0) * T(x1) * T(x2) * T(x3);
  }
  void riseY(int b, Y y) {
    static_assert(0 <= B); static_assert(B <= 4);
    assert(0 <= b); assert(b <= B);
    yRise[0] = 1;
    if (b == 0) return;
    Y y0 = y;
    yRise[1] = T(y0);
    if (b == 1) return;
    Y y1 = y + 1;
    ((y0 % 2 == 0) ? y0 : y1) /= 2;
    yRise[2] = T(y0) * T(y1);
    if (b == 2) return;
    Y y2 = y + 2;
    ((y0 % 3 == 0) ? y0 : (y1 % 3 == 0) ? y1 : y2) /= 3;
    yRise[3] = T(y0) * T(y1) * T(y2);
    if (b == 3) return;
    Y y3 = y + 3;
    ((y0 % 2 == 0) ? y0 : (y1 % 2 == 0) ? y1 : (y2 % 2 == 0) ? y2 : y3) /= 2;
    ((y0 % 2 == 0) ? y0 : (y1 % 2 == 0) ? y1 : (y2 % 2 == 0) ? y2 : y3) /= 2;
    yRise[4] = T(y0) * T(y1) * T(y2) * T(y3);
  }

  struct QueryAdd {
    int a, b;
    X x;
    Y y;
    T val;
  };
  struct QueryGet {
    X x;
    Y y;
  };
  vector<QueryAdd> qsAdd;
  vector<QueryGet> qsGet;
  vector<T> anss;
  void add(int a, int b, X x, Y y, T val) {
    assert(0 <= a); assert(a <= A);
    assert(0 <= b); assert(b <= B);
    qsAdd.push_back(QueryAdd{a, b, x, y, val});
  }
  void get(X x, Y y) {
    qsGet.push_back(QueryGet{x, y});
  }

  struct Array {
    T t[A + 1][B + 1];
    Array() : t{} {}
  };
  void run() {
    const int qsAddLen = qsAdd.size(), qsGetLen = qsGet.size();
    vector<pair<X, int>> events(qsAddLen + qsGetLen);
    for (int i = 0; i < qsAddLen; ++i) events[i] = std::make_pair(qsAdd[i].x, i);
    for (int j = 0; j < qsGetLen; ++j) events[qsAddLen + j] = std::make_pair(qsGet[j].x, qsAddLen + j);
    std::sort(events.begin(), events.end());
    vector<Y> ys(qsAddLen);
    for (int i = 0; i < qsAddLen; ++i) ys[i] = qsAdd[i].y;
    std::sort(ys.begin(), ys.end());
    ys.erase(std::unique(ys.begin(), ys.end()), ys.end());
    const int ysLen = ys.size();
    vector<Array> bit(ysLen);
    anss.assign(qsGetLen, 0);
    for (const auto &event : events) {
      if (event.second < qsAddLen) {
        const int i = event.second;
        const QueryAdd &q = qsAdd[i];
        riseX(q.a, -q.x);
        riseY(q.b, -q.y);
        T val[A + 1][B + 1];
        for (int a = 0; a <= q.a; ++a) for (int b = 0; b <= q.b; ++b) val[a][b] = q.val * xRise[q.a - a] * yRise[q.b - b];
        for (int l = std::lower_bound(ys.begin(), ys.end(), q.y) - ys.begin(); l < ysLen; l |= l + 1) {
          for (int a = 0; a <= q.a; ++a) for (int b = 0; b <= q.b; ++b) bit[l].t[a][b] += val[a][b];
        }
      } else {
        const int j = event.second - qsAddLen;
        const QueryGet &q = qsGet[j];
        riseX(A, q.x + 1);
        riseY(B, q.y + 1);
        T sum[A + 1][B + 1] = {};
        for (int l = std::upper_bound(ys.begin(), ys.end(), q.y) - ys.begin(); l > 0; l &= l - 1) {
          for (int a = 0; a <= A; ++a) for (int b = 0; b <= B; ++b) sum[a][b] += bit[l - 1].t[a][b];
        }
        for (int a = 0; a <= A; ++a) for (int b = 0; b <= B; ++b) anss[j] += sum[a][b] * xRise[a] * yRise[b];
      }
    }
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>

using std::cerr;
using std::endl;
using std::swap;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

template <int A, int B> void test(int numAdds, int numGets) {
  constexpr int LIM_POS = 100;
  constexpr long long LIM_VAL = 100;
  StaticPrefixSumAdd<int, int, long long, A, B> f;
  vector<vector<long long>> g(LIM_POS, vector<long long>(LIM_POS, 0));
  for (int i = 0; i < numAdds; ++i) {
    const int a = xrand() % (A + 1);
    const int b = xrand() % (B + 1);
    const int x = xrand() % LIM_POS;
    const int y = xrand() % LIM_POS;
    const long long val = xrand() % LIM_VAL;
    f.add(a, b, x, y, val);
    vector<vector<long long>> h(LIM_POS, vector<long long>(LIM_POS, 0));
    h[x][y] += val;
    for (int aa = 0; aa < a + 1; ++aa) {
      for (int xx = x + 1; xx < LIM_POS; ++xx) for (int yy = y; yy < LIM_POS; ++yy) {
        h[xx][yy] += h[xx - 1][yy];
      }
    }
    for (int bb = 0; bb < b + 1; ++bb) {
      for (int xx = x; xx < LIM_POS; ++xx) for (int yy = y + 1; yy < LIM_POS; ++yy) {
        h[xx][yy] += h[xx][yy - 1];
      }
    }
    for (int xx = x; xx < LIM_POS; ++xx) for (int yy = y; yy < LIM_POS; ++yy) {
      g[xx][yy] += h[xx][yy];
    }
  }
  vector<long long> expected(numGets, 0);
  for (int j = 0; j < numGets; ++j) {
    const int x = xrand() % LIM_POS;
    const int y = xrand() % LIM_POS;
    f.get(x, y);
    expected[j] += g[x][y];
  }
  f.run();
  assert(f.anss == expected);
}

void unittest() {
  {
    StaticPrefixSumAdd<int, int, int, 0, 0> f;
    f.get(0, 0);
    f.get(1, 2);
    f.get(-8, -7);
    f.run();
    assert(f.anss == vector<int>(3, 0));
  }
  {
    StaticPrefixSumAdd<int, int, int, 3, 4> f;
    f.add(0, 0, 20, 30, -10);
    f.get(19, 29);
    f.get(20, 30);
    f.get(24, 35);
    f.get(25, 34);
    f.run();
    assert(f.anss == (vector<int>{0, -10, -10, -10}));
  }
  {
    StaticPrefixSumAdd<int, int, int, 3, 4> f;
    f.add(1, 1, 20, 30, -10);
    f.get(19, 29);
    f.get(20, 30);
    f.get(24, 35);
    f.get(25, 34);
    f.run();
    assert(f.anss == (vector<int>{0, -10, -300, -300}));
  }
  {
    StaticPrefixSumAdd<int, int, int, 3, 4> f;
    f.add(2, 3, 20, 30, -10);
    f.get(19, 29);
    f.get(20, 30);
    f.get(24, 35);
    f.get(25, 34);
    f.run();
    assert(f.anss == (vector<int>{0, -10, -8400, -7350}));
  }
  test<1, 4>(20, 20);
  test<4, 1>(20, 200);
  test<4, 4>(200, 20);
  test<4, 4>(200, 200);
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
