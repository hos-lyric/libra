#include <algorithm>
#include <vector>

using std::max;
using std::vector;

// zs[i] := lcp(as[0, n), as[i, n))
// 0    i-j     j     i
// |-------|    |-------|    zs[j]
// |---| |---|  |---| |---|  zs[i-j]
template <class T> void suffixZ(const T *as, int n, int *zs) {
  if (n == 0) return;
  zs[0] = 0;
  for (int j = 0, i = 1; i < n; ++i) {
    if (i + zs[i - j] < j + zs[j]) {
      zs[i] = zs[i - j];
    } else {
      int &z = zs[i] = max(j + zs[j] - i, 0);
      for (; i + z < n && as[z] == as[i + z]; ++z) {}
      j = i;
    }
  }
  zs[0] = n;
}
template <class T> vector<int> suffixZ(const T &as) {
  vector<int> zs(as.size());
  suffixZ(as.data(), as.size(), zs.data());
  return zs;
}

////////////////////////////////////////////////////////////////////////////////

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <iostream>
#include <string>

using std::cerr;
using std::endl;
using std::string;

void unittest() {
  {
    constexpr int n = 12;
    const int as[n] = {0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0};
    int zs[n];
    suffixZ(as, n, zs);
    const int expected[n] = {12, 1, 0, 5, 1, 0, 2, 1, 0, 2, 2, 1};
    for (int i = 0; i < n; ++i) {
      assert(zs[i] == expected[i]);
    }
  }
  assert(suffixZ(vector<int>{-1, -1}) == (vector<int>{2, 1}));
  assert(suffixZ(string("")) == (vector<int>{}));
  assert(suffixZ(string("abracadabra")) ==
         (vector<int>{11, 0, 0, 1, 0, 1, 0, 4, 0, 0, 1}));
}

void yosupo__zalgorithm() {
  static char S[500'010];
  for (; ~scanf("%s", S); ) {
    const int N = strlen(S);
    vector<int> zs(N);
    suffixZ(S, N, zs.data());
    
    for (int i = 0; i < N; ++i) {
      if (i) printf(" ");
      printf("%d", zs[i]);
    }
    puts("");
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupo__zalgorithm();
  return 0;
}
