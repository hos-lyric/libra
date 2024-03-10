// TODO: speed up
// TODO: update like prime.cpp

#include <assert.h>
#include <stdio.h>
#include <algorithm>
#include <vector>

#include "../algebra/modint128.h"
#include "../other/int128.h"

using std::swap;
using std::vector;

using RMM128ForPrime = RMModInt128<-20220617>;

template <class T> vector<T> merge(const vector<T> &a, const vector<T> &b) {
  vector<T> c(a.size() + b.size());
  std::merge(a.begin(), a.end(), b.begin(), b.end(), c.begin());
  return c;
}

int bsf128(__int128 a) {
  const long long a64 = a;
  return a64 ? __builtin_ctzll(a64) : (64 + __builtin_ctzll(a >> 64));
}
__int128 gcd128(__int128 a, __int128 b) {
  if (a < 0) a = -a;
  if (b < 0) b = -b;
  if (a == 0) return b;
  if (b == 0) return a;
  const int s = bsf128(a | b);
  a >>= bsf128(a);
  do {
    b >>= bsf128(b);
    if (a > b) swap(a, b);
    b -= a;
  } while (b);
  return a << s;
}

// Checks if n is a prime using Miller-Rabin test
bool isPrime128(__int128 n) {
  if (n <= 1 || !(n & 1)) return (n == 2);
  RMM128ForPrime::setM(n);
  const int s = bsf128(n - 1);
  const __int128 d = (n - 1) >> s;
  // Based on conjectures in Zhang, Two kinds of strong pseudoprimes up to 10^36.
  for (const __int128 base : {2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
                              31, 37, 41, 43, 47, 53, 59, 61, 67, 71}) {
    if (base >= n) continue;
    RMM128ForPrime a = RMM128ForPrime(base).pow(d);
    if (a.get() == 1 || static_cast<__int128>(a.get()) == n - 1) continue;
    bool ok = false;
    for (int i = 0; i < s - 1; ++i) {
      if (static_cast<__int128>((a *= a).get()) == n - 1) {
        ok = true;
        break;
      }
    }
    if (!ok) return false;
  }
  return true;
}

// Factorize n using Pollard's rho algorithm
vector<__int128> factorize128(__int128 n) {
  static constexpr int BLOCK = 256;
  if (n <= 1) return {};
  if (isPrime128(n)) return {n};
  if (!(n & 1)) {
    const int s = bsf128(n);
    return merge(vector<__int128>(s, 2), factorize128(n >> s));
  }
  RMM128ForPrime::setM(n);
  for (__int128 c0 = 2; ; ++c0) {
    const RMM128ForPrime c = c0;
    RMM128ForPrime x, y = 2, y0, z = 1;
    __int128 d = 1;
    for (int l = 1; d == 1; l <<= 1) {
      x = y;
      for (int i = 0; i < l; ++i) y = y * y + c;
      for (int i = 0; i < l; i += BLOCK) {
        y0 = y;
        for (int j = 0; j < BLOCK && j < l - i; ++j) {
          y = y * y + c;
          z *= (y - x);
        }
        if ((d = gcd128(z.y, n)) != 1) break;
      }
    }
    if (d == n) {
      for (y = y0; ; ) {
        y = y * y + c;
        if ((d = gcd128((y - x).y, n)) != 1) break;
      }
    }
    if (d != n) return merge(factorize128(d), factorize128(n / d));
  }
}

////////////////////////////////////////////////////////////////////////////////

#include <iostream>

using std::cerr;
using std::endl;

void unittest() {
  assert(factorize128(toInt128("382785853244719627595443384812477912")) ==
         (vector<__int128>{2, 2, 2, 3, 7, 7, 7, 7, 7, 344415132826727,
                           2755321062613817}));
  // gcd128
  {
    constexpr __int128 a = 192873419827365198LL;
    constexpr __int128 b = 271982369148273947LL;
    constexpr __int128 c = 172693814726983576LL;
    assert(gcd128(a * b, a * c) == a);
  }
  assert(gcd128(static_cast<__int128>(15) << 110,
                static_cast<__int128>(21) << 101) ==
         static_cast<__int128>(3) << 101);

  // isPrime128
  assert(!isPrime128(0));
  assert(!isPrime128(1));
  for (__int128 n = 2; n < 10'000; ++n) {
    bool composite = false;
    for (__int128 d = 2; d * d <= n; ++d) {
      composite = composite || (n % d == 0);
    }
    assert(isPrime128(n) == !composite);
  }
  assert(isPrime128(9223372036854775783LL));
  assert(!isPrime128(7156857700403137441LL));
  assert(!isPrime128(toInt128("3317044064679887385961981")));
  assert(isPrime128(toInt128("1000000000000000000000000000000000000") - 159));

  // factorize128
  assert(factorize128(75600) ==
         (vector<__int128>{2, 2, 2, 2, 3, 3, 3, 5, 5, 7}));
  assert(factorize128(4294967297LL) ==
         (vector<__int128>{641, 6700417}));
  assert(factorize128(1000000016000000063LL) ==
         (vector<__int128>{1000000007, 1000000009}));
  assert(factorize128(3141592653589793238LL) ==
         (vector<__int128>{2, 3, 11, 10513, 311743, 14523877}));
  assert(factorize128(997748200186314745LL) ==
         (vector<__int128>{5, 7, 17, 17, 17581, 5610628223LL}));
  assert(factorize128(toInt128("3317044064679887385961981")) ==
         (vector<__int128>{1287836182261LL, 2575672364521LL}));
  {
    const vector<__int128> ps{
      1'000'000'000 - 117,
      1'000'000'000 - 107,
      1'000'000'000 - 71,
      1'000'000'000 - 63,
    };
    assert(factorize128(ps[0] * ps[1] * ps[2] * ps[3]) == ps);
  }
  {
    const vector<__int128> ps{
      100'000'000 - 11,
      100'000'000'000LL - 23,
      toInt128("10000000000000000000") - 39,
    };
    assert(factorize128(ps[0] * ps[1] * ps[2]) == ps);
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
