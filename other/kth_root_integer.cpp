#include <assert.h>
#include <stdio.h>
#include <algorithm>

// floor(a^(1/k))
unsigned long long floorKthRoot(unsigned long long a, unsigned long long k) {
  if (a == 0) {
    return 0;
  } else if (k <= 1) {
    return a;
  } else if (k == 2) {
    unsigned long long b = a, x = 0, y = 0;
    for (int e = (63 - __builtin_clzll(a)) & ~1; e >= 0; e -= 2) {
      x <<= 1;
      y <<= 1;
      if (b >= (y | 1) << e) {
        b -= (y | 1) << e;
        x |= 1;
        y += 2;
      }
    }
    return x;
  } else if (k <= 40) {
    // min x s.t. x^k >= 2^64
    static constexpr unsigned long long HIS[] =
        {0, 0, 4294967296ULL, 2642246, 65536, 7132, 1626, 566, 256, 139, 85, 57,
         41, 31, 24, 20, 16, 14, 12, 11, 10, 9, 8, 7, 7, 6, 6, 6, 5, 5, 5, 5,
         4, 4, 4, 4, 4, 4, 4, 4, 4};
    const int bsr = 63 - __builtin_clzll(a);
    unsigned long long lo = 1ULL << (bsr / k);
    unsigned long long hi = std::min(1ULL << (bsr / k + 1), HIS[k]);
    for (; lo + 1 < hi; ) {
      const unsigned long long mid = (lo + hi) / 2;
      unsigned long long b = mid * mid;
      for (unsigned i = 2; i < k; ++i) b *= mid;
      ((b <= a) ? lo : hi) = mid;
    }
    return lo;
  } else if (k <= 63) {
    return ((1ULL << k) <= a) ? 2 : 1;
  } else {
    return 1;
  }
}

void unittest() {
  // k = 2
  for (unsigned long long x = 0; x < 1000; ++x) {
    for (unsigned long long a = x * x; a < (x + 1) * (x + 1); ++a) {
      assert(floorKthRoot(a, 2) == x);
    }
  }
  for (unsigned long long x = 4294967295ULL - 1000; x <= 4294967295ULL; ++x) {
    for (unsigned long long a = x * x - 1000; a < x * x; ++a) {
      assert(floorKthRoot(a, 2) == x - 1);
    }
    for (unsigned long long a = x * x; a < x * x + 1000; ++a) {
      assert(floorKthRoot(a, 2) == x);
    }
  }
  for (unsigned long long b = 1; b <= 1000; ++b) {
    assert(floorKthRoot(-b, 2) == 4294967295ULL);
  }

  // general
  for (unsigned long long x = 2; x < 1000; ++x) {
    unsigned long long a = x;
    for (int k = 1; ; ++k) {
      assert(floorKthRoot(a - 1, k) == x - 1);
      assert(floorKthRoot(a, k) == x);
      if (a > ~0ULL / x) break;
      a *= x;
    }
  }
}

// https://judge.yosupo.jp/problem/kth_root_integer
int main() {
  // unittest();

  int numCases;
  scanf("%d", &numCases);
  for (int caseId = 0; caseId < numCases; ++caseId) {
    unsigned long long A, K;
    scanf("%llu%llu", &A, &K);
    printf("%llu\n", floorKthRoot(A, K));
  }
  return 0;
}
