#include <assert.h>
#include <math.h>
#include <vector>

using std::vector;

// Continued fraction of sqrt(D).
//   period: ks[1 .. $]
vector<long long> continuedFractionSqrt(long long D) {
  assert(D >= 0);
  const long long sqrtD = sqrt(static_cast<long double>(D));
  vector<long long> ks{sqrtD};
  // (sqrt(D) + a) / b, b | D - a^2
  const long long a1 = sqrtD, b1 = D - sqrtD*sqrtD;
  if (!b1) return ks;
  for (long long a = a1, b = b1; ; ) {
    const long long k = (sqrtD + a) / b;
    assert(0 <= a); assert(a <= sqrtD);
    assert(1 <= b); assert(b <= sqrtD + a);
    assert(1 <= k); assert(k <= 2 * sqrtD);
    ks.push_back(k);
    a = k * b - a;
    b = (D - a*a) / b;
    if (a == a1 && b == b1) break;
  }
  return ks;
}  // continuedFractionSqrt

////////////////////////////////////////////////////////////////////////////////

#include <iostream>

using std::cerr;
using std::endl;

void unittest() {
  assert(continuedFractionSqrt(0) == (vector<long long>{0}));
  assert(continuedFractionSqrt(1) == (vector<long long>{1}));
  assert(continuedFractionSqrt(2) == (vector<long long>{1, 2}));
  assert(continuedFractionSqrt(3) == (vector<long long>{1, 1, 2}));
  assert(continuedFractionSqrt(4) == (vector<long long>{2}));
  assert(continuedFractionSqrt(5) == (vector<long long>{2, 4}));
  assert(continuedFractionSqrt(6) == (vector<long long>{2, 2, 4}));
  assert(continuedFractionSqrt(7) == (vector<long long>{2, 1, 1, 1, 4}));
  assert(continuedFractionSqrt(8) == (vector<long long>{2, 1, 4}));
  assert(continuedFractionSqrt(9) == (vector<long long>{3}));
  assert(continuedFractionSqrt(10) == (vector<long long>{3, 6}));
  assert(continuedFractionSqrt(11) == (vector<long long>{3, 3, 6}));
  assert(continuedFractionSqrt(12) == (vector<long long>{3, 2, 6}));
  assert(continuedFractionSqrt(13) == (vector<long long>{3, 1, 1, 1, 1, 6}));
  assert(continuedFractionSqrt(14) == (vector<long long>{3, 1, 2, 1, 6}));
  assert(continuedFractionSqrt(15) == (vector<long long>{3, 1, 6}));

  for (int e = 1, ten = 10; e <= 6; ++e, ten *= 10) {
    int maxLen = 0;
    for (int D = 1; D <= ten; ++D) {
      const auto ks = continuedFractionSqrt(D);
      if (maxLen < static_cast<int>(ks.size())) maxLen = static_cast<int>(ks.size());
    }
    printf("D <= 10^%d: max |ks| = %d\n", e, maxLen);
  }
}
/*
D <= 10^1: max |ks| = 5
D <= 10^2: max |ks| = 17
D <= 10^3: max |ks| = 61
D <= 10^4: max |ks| = 218
D <= 10^5: max |ks| = 751
D <= 10^6: max |ks| = 2665
*/

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
