#include <assert.h>
#include <algorithm>
#include <utility>
#include <vector>

using std::pair;
using std::vector;

template <class X, class Y, class T> struct StaticRectAddRectSum {
  struct Rect {
    X x0, x1;
    Y y0, y1;
  };
  vector<Rect> as, bs;
  vector<T> vals, anss;
  // Adds val to [x0, x1) [y0, y1).
  //   ~~> Adds/Subtracts (X - x*) (Y - y*) val to [x*, INF) [y*, INF)
  void add(X x0, X x1, Y y0, Y y1, const T &val) {
    assert(x0 <= x1); assert(y0 <= y1);
    as.push_back(Rect{x0, x1, y0, y1});
    vals.push_back(val);
  }
  // Gets sum of [x0, x1) * [y0, y1).
  //   ~~> Gets (x*, y*)
  void get(X x0, X x1, Y y0, Y y1) {
    assert(x0 <= x1); assert(y0 <= y1);
    bs.push_back(Rect{x0, x1, y0, y1});
  }

  struct Tuple {
    T t1, tX, tY, tXY;
    Tuple() : t1(0), tX(0), tY(0), tXY(0) {}
  };
  void run() {
    const int asLen = as.size(), bsLen = bs.size();

    vector<pair<X, int>> events((asLen + bsLen) << 1);
    for (int i = 0; i < asLen; ++i) {
      events[i << 1    ] = std::make_pair(as[i].x0, i << 1    );
      events[i << 1 | 1] = std::make_pair(as[i].x1, i << 1 | 1);
    }
    for (int j = 0; j < bsLen; ++j) {
      events[(asLen + j) << 1    ] = std::make_pair(bs[j].x0, (asLen + j) << 1    );
      events[(asLen + j) << 1 | 1] = std::make_pair(bs[j].x1, (asLen + j) << 1 | 1);
    }
    std::sort(events.begin(), events.end());

    vector<Y> ys(asLen << 1);
    for (int i = 0; i < asLen; ++i) {
      ys[i << 1    ] = as[i].y0;
      ys[i << 1 | 1] = as[i].y1;
    }
    std::sort(ys.begin(), ys.end());
    ys.erase(std::unique(ys.begin(), ys.end()), ys.end());
    const int ysLen = ys.size();
    vector<Tuple> bit(ysLen);

    anss.assign(bsLen, 0);
    for (const auto &event : events) {
      if (event.second < asLen << 1) {
        const int i = event.second >> 1;
        const T valXY = (event.second & 1) ? -vals[i] : vals[i];
        const T valY = -valXY * event.first;
        {
          const T valX = -valXY * as[i].y0;
          const T val1 = -valY * as[i].y0;
          for (int l = lower_bound(ys.begin(), ys.end(), as[i].y0) - ys.begin(); l < ysLen; l |= l + 1) {
            bit[l].t1 += val1;
            bit[l].tX += valX;
            bit[l].tY += valY;
            bit[l].tXY += valXY;
          }
        }
        {
          const T valX = -valXY * as[i].y1;
          const T val1 = -valY * as[i].y1;
          for (int l = lower_bound(ys.begin(), ys.end(), as[i].y1) - ys.begin(); l < ysLen; l |= l + 1) {
            bit[l].t1 -= val1;
            bit[l].tX -= valX;
            bit[l].tY -= valY;
            bit[l].tXY -= valXY;
          }
        }
      } else {
        const int j = (event.second >> 1) - asLen;
        T val1 = 0, valX = 0;
        {
          T sum1 = 0, sumX = 0, sumY = 0, sumXY = 0;
          for (int l = std::upper_bound(ys.begin(), ys.end(), bs[j].y0) - ys.begin() - 1; l >= 0; l = (l & (l + 1)) - 1) {
            sum1 += bit[l].t1;
            sumX += bit[l].tX;
            sumY += bit[l].tY;
            sumXY += bit[l].tXY;
          }
          val1 -= (sum1 + sumY * bs[j].y0);
          valX -= (sumX + sumXY * bs[j].y0);
        }
        {
          T sum1 = 0, sumX = 0, sumY = 0, sumXY = 0;
          for (int l = std::upper_bound(ys.begin(), ys.end(), bs[j].y1) - ys.begin() - 1; l >= 0; l = (l & (l + 1)) - 1) {
            sum1 += bit[l].t1;
            sumX += bit[l].tX;
            sumY += bit[l].tY;
            sumXY += bit[l].tXY;
          }
          val1 += (sum1 + sumY * bs[j].y1);
          valX += (sumX + sumXY * bs[j].y1);
        }
        const T val = val1 + valX * event.first;
        (event.second & 1) ? (anss[j] += val) : (anss[j] -= val);
      }
    }
  }
};

////////////////////////////////////////////////////////////////////////////////

using std::swap;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void unittest() {
  {
    StaticRectAddRectSum<int, int, int> f;
    f.get(0, 0, 0, 0);
    f.get(1, 2, 3, 4);
    f.get(-8, -7, -6, -5);
    f.run();
    assert(f.anss == vector<int>(3, 0));
  }
  {
    constexpr int LIM_POS = 100;
    constexpr int LIM_VAL = 1'000'000;
    auto test = [&](int A, int B) -> void {
      StaticRectAddRectSum<int, int, long long> f;
      vector<vector<long long>> g(LIM_POS, vector<long long>(LIM_POS, 0));
      for (int a = 0; a < A; ++a) {
        int x0 = xrand() % (LIM_POS + 1);
        int x1 = xrand() % (LIM_POS + 1);
        int y0 = xrand() % (LIM_POS + 1);
        int y1 = xrand() % (LIM_POS + 1);
        if (x0 > x1) swap(x0, x1);
        if (y0 > y1) swap(y0, y1);
        const long long val = xrand() % LIM_VAL;
        f.add(x0, x1, y0, y1, val);
        for (int x = x0; x < x1; ++x) for (int y = y0; y < y1; ++y) {
          g[x][y] += val;
        }
      }
      vector<long long> brt(B, 0);
      for (int b = 0; b < B; ++b) {
        int x0 = xrand() % (LIM_POS + 1);
        int x1 = xrand() % (LIM_POS + 1);
        int y0 = xrand() % (LIM_POS + 1);
        int y1 = xrand() % (LIM_POS + 1);
        if (x0 > x1) swap(x0, x1);
        if (y0 > y1) swap(y0, y1);
        f.get(x0, x1, y0, y1);
        for (int x = x0; x < x1; ++x) for (int y = y0; y < y1; ++y) {
          brt[b] += g[x][y];
        }
      }
      f.run();
      assert(f.anss == brt);
    };
    test(20, 20);
    test(20, 200);
    test(200, 20);
    test(200, 200);
  }
}

#include <stdio.h>
#include <iostream>
using std::cerr;
using std::endl;

////////////////////////////////////////////////////////////////////////////////
template <unsigned M_> struct ModInt {
  static constexpr unsigned M = M_;
  unsigned x;
  constexpr ModInt() : x(0U) {}
  constexpr ModInt(unsigned x_) : x(x_ % M) {}
  constexpr ModInt(unsigned long long x_) : x(x_ % M) {}
  constexpr ModInt(int x_) : x(((x_ %= static_cast<int>(M)) < 0) ? (x_ + static_cast<int>(M)) : x_) {}
  constexpr ModInt(long long x_) : x(((x_ %= static_cast<long long>(M)) < 0) ? (x_ + static_cast<long long>(M)) : x_) {}
  ModInt &operator+=(const ModInt &a) { x = ((x += a.x) >= M) ? (x - M) : x; return *this; }
  ModInt &operator-=(const ModInt &a) { x = ((x -= a.x) >= M) ? (x + M) : x; return *this; }
  ModInt &operator*=(const ModInt &a) { x = (static_cast<unsigned long long>(x) * a.x) % M; return *this; }
  ModInt &operator/=(const ModInt &a) { return (*this *= a.inv()); }
  ModInt pow(long long e) const {
    if (e < 0) return inv().pow(-e);
    ModInt a = *this, b = 1U; for (; e; e >>= 1) { if (e & 1) b *= a; a *= a; } return b;
  }
  ModInt inv() const {
    unsigned a = M, b = x; int y = 0, z = 1;
    for (; b; ) { const unsigned q = a / b; const unsigned c = a - q * b; a = b; b = c; const int w = y - static_cast<int>(q) * z; y = z; z = w; }
    assert(a == 1U); return ModInt(y);
  }
  ModInt operator+() const { return *this; }
  ModInt operator-() const { ModInt a; a.x = x ? (M - x) : 0U; return a; }
  ModInt operator+(const ModInt &a) const { return (ModInt(*this) += a); }
  ModInt operator-(const ModInt &a) const { return (ModInt(*this) -= a); }
  ModInt operator*(const ModInt &a) const { return (ModInt(*this) *= a); }
  ModInt operator/(const ModInt &a) const { return (ModInt(*this) /= a); }
  template <class T> friend ModInt operator+(T a, const ModInt &b) { return (ModInt(a) += b); }
  template <class T> friend ModInt operator-(T a, const ModInt &b) { return (ModInt(a) -= b); }
  template <class T> friend ModInt operator*(T a, const ModInt &b) { return (ModInt(a) *= b); }
  template <class T> friend ModInt operator/(T a, const ModInt &b) { return (ModInt(a) /= b); }
  explicit operator bool() const { return x; }
  bool operator==(const ModInt &a) const { return (x == a.x); }
  bool operator!=(const ModInt &a) const { return (x != a.x); }
  friend std::ostream &operator<<(std::ostream &os, const ModInt &a) { return os << a.x; }
};
////////////////////////////////////////////////////////////////////////////////

// https://judge.yosupo.jp/problem/static_rectangle_add_rectangle_sum
void yosupo__static_rectangle_add_rectangle_sum() {
  constexpr unsigned MO = 998244353;
  using Mint = ModInt<MO>;

  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    StaticRectAddRectSum<int, int, Mint> f;
    for (int i = 0; i < N; ++i) {
      int x0, x1, y0, y1;
      Mint val;
      scanf("%d%d%d%d%u", &x0, &y0, &x1, &y1, &val.x);  // y0 x1
      f.add(x0, x1, y0, y1, val);
    }
    for (int q = 0; q < Q; ++q) {
      int x0, x1, y0, y1;
      scanf("%d%d%d%d", &x0, &y0, &x1, &y1);  // y0 x1
      f.get(x0, x1, y0, y1);
    }
    f.run();
    for (int q = 0; q < Q; ++q) {
      printf("%u\n", f.anss[q].x);
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupo__static_rectangle_add_rectangle_sum();
  return 0;
}
