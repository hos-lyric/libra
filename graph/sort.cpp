#include <utility>
#include <vector>

using std::vector;

// Sorts [first, last) so that for any adjacent elements a, b in this order,
// comp(a, b) || !comp(b, a)
//   [buffer, buffer + floor((last - first) / 2))  must be available.
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

////////////////////////////////////////////////////////////////////////////////

#include <assert.h>
#include <functional>

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void unittest() {
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
        vector<int> buf(N / 2);
        mergeSort(us, [&](int u, int v) -> bool {
          return (graph[u][v] == '1');
        });
        vector<int> cnt(N, 0);
        for (int j = 0; j < N; ++j) {
          assert(0 <= us[j]); assert(us[j] < N);
          ++cnt[us[j]];
        }
        for (int u = 0; u < N; ++u) {
          assert(cnt[u] == 1);
        }
        for (int j = 0; j < N - 1; ++j) {
          assert(graph[us[j]][us[j + 1]] || !graph[us[j + 1]][us[j]]);
        }
      }
    }
  }
}

int main() {
  unittest();
  return 0;
}
