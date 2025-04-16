#include <assert.h>
#include <string>
#include <vector>

using std::string;
using std::vector;

// n * n grid, '.': connected, '#': not adjacent
int heyawakeMaxValue(int n) {
  assert(n >= 2);
  if (n == 3) return 4;
  return (n*n + 1 + n%2) / 3;
}
vector<string> heyawakeMax(int n) {
  static const vector<string> SMALL[8] = {{}, {}, {
    "#.",
    "..",
  }, {
    "#.#",
    "...",
    "#.#",
  }, {
    "#..#",
    ".#..",
    "....",
    "#..#",
  }, {
    "#.#.#",
    ".....",
    "#.#.#",
    ".....",
    "#.#.#",
  }, {
    "#..#.#",
    "..#...",
    "#...#.",
    ".#...#",
    "...#..",
    "#.#..#",
  }, {
    "#...#.#",
    ".#.#...",
    "..#.#.#",
    "#......",
    "..#.#.#",
    ".#.#...",
    "#...#.#",
  }};
  static const vector<string> INSIDE[8] = {{}, {}, SMALL[2], {
    "#.#",
    "...",
    "..#",
  }, SMALL[4], {
    "#...#",
    ".#.#.",
    "..#..",
    ".#.#.",
    "#...#",
  }, SMALL[6], SMALL[7]};
  assert(n >= 2);
  if (n <= 7) return SMALL[n];
  vector<string> a(n, string(n, '.'));
  for (int m = n, off = 0; ; m -= 6, off += 3) {
    if (m <= 7) {
      for (int x = 0; x < m; ++x) for (int y = 0; y < m; ++y) a[off + x][off + y] = INSIDE[m][x][y];
      return a;
    } else if (m % 2 != 0) {
      const int l = m / 4;
      for (int i = 0; i < l; ++i) {
        a[off + i*2][off + 0] = a[off + i*2][off + 2] = '#';
      }
      a[off + l*2 - 1][off + 1] = '#';
      a[off + l*2 + 1][off + 0] = a[off + l*2 + 2][off + 1] = a[off + l*2 + 1][off + 2] = '#';
      for (int i = l + 2; i <= m / 2; ++i) {
        a[off + i*2][off + 0] = a[off + i*2][off + 2] = '#';
      }
      for (int x = 0; x <= m - 1; x += 2) {
        a[off + x][off + m - 1] = a[off + x][off + m - 3] = '#';
      }
      for (int y = 4; y <= m - 5; y += 2) {
        a[off + 0][off + y] = a[off + 2][off + y] = '#';
        a[off + m - 1][off + y] = a[off + m - 3][off + y] = '#';
      }
    } else {
      const int l = (m + 2) / 4;
      for (int i = 0; i < l; ++i) {
        a[off + i*2][off + 0] = a[off + i*2][off + 2] = '#';
        a[off + m - 1][off + i*2] = a[off + m - 3][off + i*2] = '#';
        a[off + m - 1 - i*2][off + m - 1] = a[off + m - 1 - i*2][off + m - 3] = '#';
        a[off + 0][off + m - 1 - i*2] = a[off + 2][off + m - 1 - i*2] = '#';
      }
      a[off + l*2 - 1][off + 1] = '#';
      a[off + m - 2][off + l*2 - 1] = '#';
      a[off + m - 1 - l*2 + 1][off + m - 2] = '#';
      a[off + 1][off + m - 1 - l*2 + 1] = '#';
      for (int i = l; i < m / 2 - 2; ++i) {
        a[off + i*2 + 1][off + 0] = a[off + i*2 + 1][off + 2] = '#';
        a[off + m - 1][off + i*2 + 1] = a[off + m - 3][off + i*2 + 1] = '#';
        a[off + m - 1 - i*2 - 1][off + m - 1] = a[off + m - 1 - i*2 - 1][off + m - 3] = '#';
        a[off + 0][off + m - 1 - i*2 - 1] = a[off + 2][off + m - 1 - i*2 - 1] = '#';
      }
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <utility>

using std::cerr;
using std::endl;
using std::pair;

void unittest() {
  for (int n = 2; n <= 23; ++n) {
    const int value = heyawakeMaxValue(n);
    const auto a = heyawakeMax(n);
    cerr << n << " " << value << endl;
    for (int x = 0; x < n; ++x) cerr << a[x] << endl;
  }
  for (int n = 2; n <= 100; ++n) {
    const int value = heyawakeMaxValue(n);
    const auto a = heyawakeMax(n);
    assert(static_cast<int>(a.size()) == n);
    for (int x = 0; x < n; ++x) assert(static_cast<int>(a[x].size()) == n);
    for (int x = 0; x < n; ++x) for (int y = 0; y < n; ++y) assert(a[x][y] == '.' || a[x][y] == '#');
    int cnt = 0;
    for (int x = 0; x < n; ++x) for (int y = 0; y < n; ++y) if (a[x][y] == '#') ++cnt;
    assert(cnt == value);
    vector<vector<int>> vis(n, vector<int>(n, 0));
    [&]() -> void {
      for (int x0 = 0; x0 < n; ++x0) for (int y0 = 0; y0 < n; ++y0) if (a[x0][y0] == '.') {
        vector<pair<int, int>> stack;
        vis[x0][y0] = 1;
        stack.emplace_back(x0, y0);
        for (; stack.size(); ) {
          const int x = stack.back().first;
          const int y = stack.back().second;
          stack.pop_back();
          auto visit = [&](int xx, int yy) -> void {
            if (0 <= xx && xx < n && 0 <= yy && yy < n && !vis[xx][yy]) {
              vis[xx][yy] = 1;
              stack.emplace_back(xx, yy);
            }
          };
          visit(x + 1, y);
          visit(x, y + 1);
          visit(x - 1, y);
          visit(x, y - 1);
        }
        return;
      }
    }();
    for (int x = 0; x < n; ++x) for (int y = 0; y < n; ++y) if (a[x][y] == '.') assert(vis[x][y]);
    for (int x = 0; x < n - 1; ++x) for (int y = 0; y < n; ++y) assert(!(a[x][y] == '#' && a[x + 1][y] == '#'));
    for (int x = 0; x < n; ++x) for (int y = 0; y < n - 1; ++y) assert(!(a[x][y] == '#' && a[x][y + 1] == '#'));
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
