#include <assert.h>
#include <stdio.h>
#include <algorithm>
#include <utility>
#include <vector>

using std::pair;
using std::swap;
using std::vector;

template <class T> T power(T a, long long e, T m) {
  for (T b = 1; ; (a *= a) %= m) {
    if (e & 1) (b *= a) %= m;
    if (!(e >>= 1)) return b;
  }
}

long long gcd(long long a, long long b) {
  if (a < 0) a = -a;
  if (b < 0) b = -b;
  if (a == 0) return b;
  if (b == 0) return a;
  const int s = __builtin_ctzll(a | b);
  a >>= __builtin_ctzll(a);
  do {
    b >>= __builtin_ctzll(b);
    if (a > b) swap(a, b);
    b -= a;
  } while (b);
  return a << s;
}

bool isPrime(long long n) {
  if (n <= 1 || n % 2 == 0) return (n == 2);
  const int s = __builtin_ctzll(n - 1);
  const long long d = (n - 1) >> s;
  // http://miller-rabin.appspot.com/
  for (const long long base : {2, 325, 9375, 28178, 450775, 9780504, 1795265022}) {
    __int128 a = base % n;
    if (a == 0) continue;
    a = power<__int128>(a, d, n);
    if (a == 1 || a == n - 1) continue;
    bool ok = false;
    for (int i = 0; i < s - 1; ++i) {
      (a *= a) %= n;
      if (a == n - 1) {
        ok = true;
        break;
      }
    }
    if (!ok) return false;
  }
  return true;
}

// n >= 3, odd
void factorizeRec(long long n, vector<long long> &ps) {
  static constexpr int BLOCK = 256;
  if (isPrime(n)) {
    ps.push_back(n);
  } else {
    for (long long c = 2; ; ++c) {
      long long x, y = 2, y0, z = 1, d = 1;
      for (int l = 1; d == 1; l <<= 1) {
        x = y;
        for (int i = 0; i < l; ++i) y = (static_cast<__int128>(y) * y + c) % n;
        for (int i = 0; i < l; i += BLOCK) {
          y0 = y;
          for (int j = 0; j < BLOCK && j < l - i; ++j) {
            y = (static_cast<__int128>(y) * y + c) % n;
            z = (static_cast<__int128>(z) * (y - x)) % n;
          }
          if ((d = gcd(z, n)) != 1) break;
        }
      }
      if (d == n) {
        for (y = y0; ; ) {
          y = (static_cast<__int128>(y) * y + c) % n;
          if ((d = gcd(y - x, n)) != 1) break;
        }
      }
      if (d != n) {
        factorizeRec(d, ps);
        factorizeRec(n / d, ps);
        return;
      }
    }
  }
}

vector<pair<long long, int>> factorize(long long n) {
  vector<pair<long long, int>> pes;
  if (n >= 2) {
    const int s = __builtin_ctzll(n);
    if (s) pes.emplace_back(2, s);
    if (n >> s >= 2) {
      vector<long long> ps;
      factorizeRec(n >> s, ps);
      std::sort(ps.begin(), ps.end());
      const int psLen = ps.size();
      for (int i = 0, j = 0; i < psLen; i = j) {
        for (; j < psLen && ps[i] == ps[j]; ++j) {}
        pes.emplace_back(ps[i], j - i);
      }
    }
  }
  return pes;
}

vector<long long> divisors(long long n) {
  const auto pes = factorize(n);
  vector<long long> ds{1};
  for (const auto &pe : pes) {
    const int len0 = ds.size();
    const int len1 = len0 * (pe.second + 1);
    ds.resize(len1);
    for (int i = len0; i < len1; ++i) ds[i] = ds[i - len0] * pe.first;
  }
  std::sort(ds.begin(), ds.end());
  return ds;
}

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <iostream>

using std::cerr;
using std::endl;
using std::make_pair;

void unittest() {
  // gcd
  for (long long a = -100; a <= 100; ++a) for (long long b = -100; b <= 100; ++b) {
    long long g;
    if (a == 0 && b == 0) {
      g = 0;
    } else {
      for (g = 100; ; --g) if (a % g == 0 && b % g == 0) break;
    }
    assert(gcd(a, b) == g);
  }

  // isPrime
  assert(!isPrime(0));
  assert(!isPrime(1));
  for (long long n = 2; n <= 100000; ++n) {
    bool composite = false;
    for (long long d = 2; d * d <= n; ++d) {
      composite = composite || (n % d == 0);
    }
    assert(isPrime(n) == !composite);
  }
  assert(isPrime(9223372036854775783LL));
  assert(!isPrime(7156857700403137441LL));

  // factorize
  assert(factorize(75600) == (vector<pair<long long, int>>{
    make_pair(2, 4), make_pair(3, 3), make_pair(5, 2), make_pair(7, 1)
  }));
  assert(factorize(998244353) == (vector<pair<long long, int>>{
    make_pair(998244353, 1)
  }));
  assert(factorize(4294967297LL) == (vector<pair<long long, int>>{
    make_pair(641, 1), make_pair(6700417, 1)
  }));
  assert(factorize(1000000016000000063LL) == (vector<pair<long long, int>>{
    make_pair(1000000007, 1), make_pair(1000000009, 1)
  }));
  assert(factorize(3141592653589793238LL) == (vector<pair<long long, int>>{
    make_pair(2, 1), make_pair(3, 1), make_pair(11, 1), make_pair(10513, 1),
    make_pair(311743, 1), make_pair(14523877, 1)
  }));
  assert(factorize(997748200186314745LL) == (vector<pair<long long, int>>{
    make_pair(5, 1), make_pair(7, 1), make_pair(17, 2), make_pair(17581, 1),
    make_pair(5610628223LL, 1)
  }));

  // divisors
  for (long long n = 1; n <= 1000; ++n) {
    vector<long long> expected;
    for (long long d = 1; d <= n; ++d) if (n % d == 0) expected.push_back(d);
    assert(divisors(n) == expected);
  }
  assert(divisors(998244353) == (vector<long long>{1, 998244353}));
  assert(divisors(4000000064000000252LL) == (vector<long long>{
    1, 2, 4,
    1000000007, 1000000009, 2000000014, 2000000018, 4000000028, 4000000036,
    1000000016000000063LL, 2000000032000000126LL, 4000000064000000252LL
  }));
}

// https://judge.yosupo.jp/problem/factorize
void yosupo_factorize() {
  for (int numCases; ~scanf("%d", &numCases); ) {
    for (int caseId = 0; caseId < numCases; ++caseId) {
      long long n;
      scanf("%lld", &n);
      const auto pes = factorize(n);
      int sumE = 0;
      for (const pair<long long, int> &pe : pes) {
        sumE += pe.second;
      }
      printf("%d", sumE);
      for (const pair<long long, int> &pe : pes) {
        for (int i = 0; i < pe.second; ++i) {
          printf(" %lld", pe.first);
        }
      }
      puts("");
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupo_factorize();
  return 0;
}
