#include <assert.h>
#include <algorithm>
#include <utility>
#include <vector>

using std::pair;
using std::vector;

template <class X, class Y, class T> struct StaticRectAddPointSum {
  struct Rect {
    X x0, x1;
    Y y0, y1;
  };
  vector<Rect> as;
  vector<pair<X, Y>> bs;
  vector<T> vals, anss;
  // Adds val to [x0, x1) [y0, y1).
  //   ~~> Adds to (x*, y*)
  void add(X x0, X x1, Y y0, Y y1, const T &val) {
    assert(x0 <= x1); assert(y0 <= y1);
    as.push_back(Rect{x0, x1, y0, y1});
    vals.push_back(val);
  }
  // Gets sum at (x, y).
  void get(X x, Y y) {
    bs.emplace_back(x, y);
  }

  void run() {
    const int asLen = as.size(), bsLen = bs.size();

    // same x ==> add then get
    vector<pair<X, int>> events((asLen << 1) + bsLen);
    for (int i = 0; i < asLen; ++i) {
      events[i << 1    ] = std::make_pair(as[i].x0, i << 1    );
      events[i << 1 | 1] = std::make_pair(as[i].x1, i << 1 | 1);
    }
    for (int j = 0; j < bsLen; ++j) {
      events[(asLen << 1) + j] = std::make_pair(bs[j].first, (asLen << 1) + j);
    }
    std::sort(events.begin(), events.end());

    vector<Y> ys(bsLen);
    for (int j = 0; j < bsLen; ++j) {
      ys[j] = bs[j].second;
    }
    std::sort(ys.begin(), ys.end());
    ys.erase(std::unique(ys.begin(), ys.end()), ys.end());
    const int ysLen = ys.size();
    vector<T> bit(ysLen, 0);

    anss.assign(bsLen, 0);
    for (const auto &event : events) {
      if (event.second >= asLen << 1) {
        const int j = event.second - (asLen << 1);
        T sum = 0;
        for (int l = std::lower_bound(ys.begin(), ys.end(), bs[j].second) - ys.begin() + 1; l > 0; l &= l - 1) {
          sum += bit[l - 1];
        }
        anss[j] = sum;
      } else {
        const int i = event.second >> 1;
        const T val = (event.second & 1) ? -vals[i] : vals[i];
        for (int l = std::lower_bound(ys.begin(), ys.end(), as[i].y0) - ys.begin(); l < ysLen; l |= l + 1) {
          bit[l] += val;
        }
        for (int l = std::lower_bound(ys.begin(), ys.end(), as[i].y1) - ys.begin(); l < ysLen; l |= l + 1) {
          bit[l] -= val;
        }
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

void unittest() {
  {
    StaticRectAddPointSum<int, int, int> f;
    f.run();
    assert(f.anss == (vector<int>{}));
  }
  {
    StaticRectAddPointSum<int, int, int> f;
    f.get(0, 0);
    f.get(1, 2);
    f.get(-8, -7);
    f.run();
    assert(f.anss == (vector<int>{0, 0, 0}));
  }
  {
    StaticRectAddPointSum<int, int, int> f;
    f.add(0, 0, 0, 0, -11);
    f.add(1, 2, 3, 4, 12);
    f.add(-8, -7, -6, -5, 14);
    f.run();
    assert(f.anss == (vector<int>{}));
  }
  {
    StaticRectAddPointSum<int, int, int> f;
    f.add(0, 0, 0, 0, -1);
    f.add(4, 5, 7, 9, -10);
    f.get(3, 9);
    f.get(4, 8);
    f.get(4, 7);
    f.get(5, 6);
    f.run();
    assert(f.anss == (vector<int>{0, -10, -10, 0}));
  }
  {
    constexpr int LIM_POS = 100;
    constexpr long long LIM_VAL = 1'000'000'000;
    auto test = [&](int A, int B) -> void {
      StaticRectAddPointSum<int, int, long long> f;
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
        const int x = xrand() % LIM_POS;
        const int y = xrand() % LIM_POS;
        f.get(x, y);
        brt[b] = g[x][y];
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

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
