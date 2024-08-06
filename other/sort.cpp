#include <assert.h>
#include <utility>
#include <vector>

using std::pair;
using std::vector;

// Sorts [first, last) so that for any adjacent elements a, b in this order,
// comp(a, b) || !comp(b, a)
//   [buffer, buffer + floor((last - first) / 2))  must be available.
//   <= (n (ceil(log_2 n) - 1) + 1) calls to comp for n = last - first >= 1
template <class Iter, class Comp>
void mergeSort(Iter first, Iter last, Iter buffer, Comp comp) {
  if (last - first >= 2) {
    Iter middle = first + (last - first) / 2;
    mergeSort(first, middle, buffer, comp);
    mergeSort(middle, last, buffer, comp);
    Iter i = first, j = first, k = buffer, l = buffer;
    for (; j != middle; ) *l++ = std::move(*j++);
    for (; k != l && j != last; ) *i++ = comp(*j, *k) ? *j++ : *k++;
    for (; k != l; ) *i++ = std::move(*k++);
  }
}
template <class T, class Comp> void mergeSort(T *first, T *last, Comp comp) {
  vector<T> buffer((last - first) / 2);
  mergeSort(first, last, buffer.data(), comp);
}
template <class T, class Comp> void mergeSort(vector<T> &as, Comp comp) {
  vector<T> buffer(as.size() / 2);
  mergeSort(as.begin(), as.end(), buffer.begin(), comp);
}

// Each operation consists of disjoint pairs (compare and swap).
// Batcher's algorithm
// (1 + 2 + ... + ceil(log_2(n))) operations
vector<vector<pair<int, int>>> parallelSort(int n) {
  assert(n >= 0);
  vector<vector<pair<int, int>>> ops;
  for (int m = 1; m < n; m <<= 1) {
    // sorted blocks of m elements
    for (int d = m; d >= 1; d >>= 1) {
      // operate on pairs of distance d
      ops.emplace_back();
      for (int i = 0; i < n; i += (m << 1)) {
        for (int j = i + d % m; j + d < i + (m << 1); j += (d << 1)) {
          for (int k = j; k < j + d && k + d < n; ++k) {
            ops.back().emplace_back(k, k + d);
          }
        }
      }
    }
  }
  return ops;
}

////////////////////////////////////////////////////////////////////////////////

#include <functional>
#include <iostream>

using std::cerr;
using std::endl;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void unittest_mergeSort() {
  {
    vector<int> seqs[6]{
      {3, 1, 4, 1, 5, 9},
      {2, 6, 5, 3, 5},
      {8, 9, 7, 9},
      {3, 2, 3},
      {8, 4},
      {6},
    };
    mergeSort(seqs, seqs + 6, std::less<vector<int>>());
    assert(seqs[0] == (vector<int>{2, 6, 5, 3, 5}));
    assert(seqs[1] == (vector<int>{3, 1, 4, 1, 5, 9}));
    assert(seqs[2] == (vector<int>{3, 2, 3}));
    assert(seqs[3] == (vector<int>{6}));
    assert(seqs[4] == (vector<int>{8, 4}));
    assert(seqs[5] == (vector<int>{8, 9, 7, 9}));
  }
  {
    for (int N = 0; N <= 100; ++N) {
      int e = 0;
      for (; !(N <= 1 << e); ++e) {}
      for (int caseId = 0; caseId < 100; ++caseId) {
        vector<vector<char>> graph(N, vector<char>(N, '0'));
        for (int u = 0; u < N; ++u) for (int v = u + 1; v < N; ++v) {
          switch (xrand() % 3) {
            case 0: break;
            case 1: graph[u][v] = '1'; break;
            case 2: graph[v][u] = '1'; break;
            default: assert(false);
          }
        }
        vector<int> us(N);
        for (int j = 0; j < N; ++j) {
          us[j] = j;
        }
        int numCalls = 0;
        mergeSort(us, [&](int u, int v) -> bool {
          ++numCalls;
          return (graph[u][v] == '1');
        });
        assert(numCalls <= N * (e - 1) + 1);
        vector<int> cnt(N, 0);
        for (int j = 0; j < N; ++j) {
          assert(0 <= us[j]); assert(us[j] < N);
          ++cnt[us[j]];
        }
        for (int u = 0; u < N; ++u) {
          assert(cnt[u] == 1);
        }
        for (int j = 0; j < N - 1; ++j) {
          assert(graph[us[j]][us[j + 1]] == '1' || graph[us[j + 1]][us[j]] != '1');
        }
      }
    }
  }
}

void unittest_parallelSort() {
  assert(parallelSort(0) == (vector<vector<pair<int, int>>>{}));
  assert(parallelSort(1) == (vector<vector<pair<int, int>>>{}));
  assert(parallelSort(2) == (vector<vector<pair<int, int>>>{
    {{0, 1}},
  }));
  assert(parallelSort(8) == (vector<vector<pair<int, int>>>{
    {{0, 1}, {2, 3}, {4, 5}, {6, 7}},
    {{0, 2}, {1, 3}, {4, 6}, {5, 7}},
    {{1, 2}, {5, 6}},
    {{0, 4}, {1, 5}, {2, 6}, {3, 7}},
    {{2, 4}, {3, 5}},
    {{1, 2}, {3, 4}, {5, 6}},
  }));
  for (int n = 0; n <= 20; ++n) {
    const vector<vector<pair<int, int>>> ops = parallelSort(n);
    for (const auto &op : ops) {
      assert(op.size() >= 1);
      vector<int> used(n, 0);
      for (const auto &o : op) {
        assert(0 <= o.first); assert(o.first < n);
        assert(0 <= o.second); assert(o.second < n);
        assert(o.first < o.second);
        assert(!used[o.first]); used[o.first] = 1;
        assert(!used[o.second]); used[o.second] = 1;
      }
    }
    for (int p = 0; p < 1 << n; ++p) {
      int q = p;
      for (const auto &op : ops) {
        for (const auto &o : op) {
          if (!(q >> o.first & 1) && (q >> o.second & 1)) {
            q ^= 1 << o.first ^ 1 << o.second;
          }
        }
      }
      assert(!(q & (q + 1)));
    }
  }
}

int main() {
  unittest_mergeSort(); cerr << "PASSED unittest_mergeSort" << endl;
  unittest_parallelSort(); cerr << "PASSED unittest_parallelSort" << endl;
  return 0;
}
