#include <assert.h>
#include <utility>
#include <vector>

using std::pair;
using std::vector;

// https://oeis.org/A000081
constexpr int UNLABELED_ROOTED[26] = {0, 1, 1, 2, 4, 9, 20, 48, 115, 286, 719, 1842, 4766, 12486, 32973, 87811, 235381, 634847, 1721159, 4688676, 12826228, 35221832, 97055181, 268282855, 743724984, 2067174645};
// https://oeis.org/A000055
constexpr int UNLABELED_UNROOTED[29] = {0, 1, 1, 1, 2, 3, 6, 11, 23, 47, 106, 235, 551, 1301, 3159, 7741, 19320, 48629, 123867, 317955, 823065, 2144505, 5623756, 14828074, 39299897, 104636890, 279793450, 751065460, 2023443032};

namespace enu_tree {
constexpr int MAX_N = 21;

using Id = pair<int, int>;

// (largest subtree, remaining tree)
vector<pair<Id, Id>> T[MAX_N + 1];

inline int TLen(int n) {
  return T[n].size();
}

// tie-break (n/2) + (n/2)
inline bool isCentroid(int n, int x) {
  return (T[n][x].first <= T[n][x].second);
}

// |non-root subtree| <= limDn
void build(int limDn = MAX_N - 1) {
  for (int n = 0; n <= MAX_N; ++n) T[n].clear();
  T[1].emplace_back(Id(0, 0), Id(0, 0));
  for (int dn = 1; dn < MAX_N && dn <= limDn; ++dn) for (int dx = 0; dx < TLen(dn); ++dx) {
    for (int n = 1; n + dn <= MAX_N; ++n) for (int x = 0; x < TLen(n); ++x) {
      T[n + dn].emplace_back(Id(dn, dx), Id(n, x));
    }
  }
}

void getParDfs(int n, int x, int p, int &id, vector<int> &par) {
  const int u = id++;
  par[u] = p;
  for (int nn = n, xx = x; nn > 1; ) {
    const auto &t = T[nn][xx];
    getParDfs(t.first.first, t.first.second, u, id, par);
    nn = t.second.first;
    xx = t.second.second;
  }
}
vector<int> getPar(int n, int x) {
  assert(1 <= n); assert(n <= MAX_N);
  assert(0 <= x); assert(x < TLen(n));
  int id = 0;
  vector<int> par(n, -1);
  getParDfs(n, x, -1, id, par);
  return par;
}
vector<int> getPar(const Id &id) {
  return getPar(id.first, id.second);
}
}  // enu_tree

////////////////////////////////////////////////////////////////////////////////

#include <iostream>

using std::cerr;
using std::endl;

void unittest() {
  using namespace enu_tree;

  build(998244353);
  for (int n = 0; n <= MAX_N; ++n) {
    int numUnrooted = 0;
    for (int x = 0; x < TLen(n); ++x) if (isCentroid(n, x)) ++numUnrooted;
    cerr << n << ": " << TLen(n) << " " << numUnrooted << endl;
    assert(TLen(n) == UNLABELED_ROOTED[n]);
    assert(numUnrooted == UNLABELED_UNROOTED[n]);
  }
  assert(getPar(1, 0) == (vector<int>{-1}));
  assert(getPar(2, 0) == (vector<int>{-1, 0}));
  assert(getPar(3, 0) == (vector<int>{-1, 0, 0}));
  assert(getPar(3, 1) == (vector<int>{-1, 0, 1}));
  assert(getPar(4, 0) == (vector<int>{-1, 0, 0, 0}));
  assert(getPar(4, 1) == (vector<int>{-1, 0, 1, 0}));
  assert(getPar(4, 2) == (vector<int>{-1, 0, 1, 1}));
  assert(getPar(4, 3) == (vector<int>{-1, 0, 1, 2}));

  build(MAX_N / 2);
  for (int n = 0; n <= MAX_N; ++n) {
    int numUnrooted = 0;
    for (int x = 0; x < TLen(n  ); ++x) if (isCentroid(n, x)) ++numUnrooted;
    cerr << n << ": " << TLen(n) << " " << numUnrooted << endl;
    assert(TLen(n) <= UNLABELED_ROOTED[n]);
    assert(numUnrooted == UNLABELED_UNROOTED[n]);
  }
  assert(getPar(1, 0) == (vector<int>{-1}));
  assert(getPar(2, 0) == (vector<int>{-1, 0}));
  assert(getPar(3, 0) == (vector<int>{-1, 0, 0}));
  assert(getPar(3, 1) == (vector<int>{-1, 0, 1}));
  assert(getPar(4, 0) == (vector<int>{-1, 0, 0, 0}));
  assert(getPar(4, 1) == (vector<int>{-1, 0, 1, 0}));
  assert(getPar(4, 2) == (vector<int>{-1, 0, 1, 1}));
  assert(getPar(4, 3) == (vector<int>{-1, 0, 1, 2}));
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
