#include <assert.h>
#include <algorithm>
#include <utility>
#include <vector>

using std::pair;
using std::vector;

template <class X, class Y, class T> struct StaticPointAddRectSum {
  struct Rect {
    X x0, x1;
    Y y0, y1;
  };
  vector<pair<X, Y>> as;
  vector<Rect> bs;
  vector<T> vals, anss;
  // Adds val to (x, y).
  void add(X x, Y y, const T &val) {
    as.emplace_back(x, y);
    vals.push_back(val);
  }
  // Gets sum of [x0, x1) * [y0, y1).
  //   ~~> Gets (x*, y*)
  void get(X x0, X x1, Y y0, Y y1) {
    assert(x0 <= x1); assert(y0 <= y1);
    bs.push_back(Rect{x0, x1, y0, y1});
  }

  void run() {
    const int asLen = as.size(), bsLen = bs.size();

    // same x ==> get then add
    vector<pair<X, int>> events((bsLen << 1) + asLen);
    for (int i = 0; i < asLen; ++i) {
      events[(bsLen << 1) + i] = std::make_pair(as[i].first, (bsLen << 1) + i);
    }
    for (int j = 0; j < bsLen; ++j) {
      events[j << 1    ] = std::make_pair(bs[j].x0, j << 1    );
      events[j << 1 | 1] = std::make_pair(bs[j].x1, j << 1 | 1);
    }
    std::sort(events.begin(), events.end());

    vector<Y> ys(asLen);
    for (int i = 0; i < asLen; ++i) {
      ys[i] = as[i].second;
    }
    std::sort(ys.begin(), ys.end());
    ys.erase(std::unique(ys.begin(), ys.end()), ys.end());
    const int ysLen = ys.size();
    vector<T> bit(ysLen, 0);

    anss.assign(bsLen, 0);
    for (const auto &event : events) {
      if (event.second >= bsLen << 1) {
        const int i = event.second - (bsLen << 1);
        for (int l = std::lower_bound(ys.begin(), ys.end(), as[i].second) - ys.begin(); l < ysLen; l |= l + 1) {
          bit[l] += vals[i];
        }
      } else {
        const int j = event.second >> 1;
        T sum = 0;
        for (int l = std::lower_bound(ys.begin(), ys.end(), bs[j].y0) - ys.begin(); l > 0; l &= l - 1) {
          sum -= bit[l - 1];
        }
        for (int l = std::lower_bound(ys.begin(), ys.end(), bs[j].y1) - ys.begin(); l > 0; l &= l - 1) {
          sum += bit[l - 1];
        }
        (event.second & 1) ? (anss[j] += sum) : (anss[j] -= sum);
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
    StaticPointAddRectSum<int, int, int> f;
    f.get(0, 0, 0, 0);
    f.get(1, 2, 3, 4);
    f.get(-8, -7, -6, -5);
    f.run();
    assert(f.anss == (vector<int>{0, 0, 0}));
  }
  {
    StaticPointAddRectSum<int, int, int> f;
    f.add(3, 9, -1);
    f.add(4, 8, -10);
    f.add(4, 7, -100);
    f.add(5, 6, -1000);
    f.get(0, 0, 0, 0);
    f.get(4, 5, 7, 9);
    f.run();
    assert(f.anss == (vector<int>{0, -110}));
  }
  {
    constexpr int LIM_POS = 100;
    constexpr int LIM_VAL = 1'000'000;
    auto test = [&](int A, int B) -> void {
      StaticPointAddRectSum<int, int, long long> f;
      vector<vector<long long>> g(LIM_POS, vector<long long>(LIM_POS, 0));
      for (int a = 0; a < A; ++a) {
        const int x = xrand() % LIM_POS;
        const int y = xrand() % LIM_POS;
        const long long val = xrand() % LIM_VAL;
        f.add(x, y, val);
        g[x][y] += val;
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

#include <iostream>
using std::cerr;
using std::endl;

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
