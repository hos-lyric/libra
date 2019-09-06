#include <assert.h>
#include <stdio.h>
#include <algorithm>
#include <vector>

using std::vector;

using Int = long long;

template<class T> vector<T> merge(const vector<T> &a, const vector<T> &b) {
  vector<T> c(a.size() + b.size());
  std::merge(a.begin(), a.end(), b.begin(), b.end(), c.begin());
  return c;
}

template<class T> T power(T a, Int e, T m) {
  T b = 1;
  for (; e; e >>= 1) {
    if (e & 1) b = (b * a) % m;
    a = (a * a) % m;
  }
  return b;
}

Int gcd(Int a, Int b) {
  if (a < 0) a = -a;
  if (b < 0) b = -b;
  if (a == 0) return b;
  if (b == 0) return a;
  const int s = __builtin_ctzll(a | b);
  a >>= __builtin_ctzll(a);
  do {
    b >>= __builtin_ctzll(b);
    if (a > b) std::swap(a, b);
    b -= a;
  } while (b);
  return a << s;
}

// Checks if n is a prime using Miller-Rabin test
bool isPrime(Int n) {
  if (n <= 1 || n % 2 == 0) return (n == 2);
  const int s = __builtin_ctzll(n - 1);
  const Int d = (n - 1) >> s;
  // http://miller-rabin.appspot.com/
  for (const Int base : {2, 325, 9375, 28178, 450775, 9780504, 1795265022}) {
    __int128_t a = base % n;
    if (a == 0) continue;
    a = power<__int128_t>(a, d, n);
    if (a == 1 || a == n - 1) continue;
    bool ok = false;
    for (int i = 0; i < s - 1; ++i) {
      a = (a * a) % n;
      if (a == n - 1) {
        ok = true;
        break;
      }
    }
    if (!ok) return false;
  }
  return true;
}

// Factorize n using Pollard's rho algorithm
vector<Int> factorize(Int n) {
  if (n <= 1) return {};
  if (isPrime(n)) return {n};
  if (n % 2 == 0) return merge({2}, factorize(n / 2));
  for (Int c = 1; ; ++c) {
    Int x = 2, y = 2, d;
    do {
      x = (static_cast<__int128_t>(x) * x + c) % n;
      y = (static_cast<__int128_t>(y) * y + c) % n;
      y = (static_cast<__int128_t>(y) * y + c) % n;
      d = gcd(x - y, n);
    } while (d == 1);
    if (d < n) return merge(factorize(d), factorize(n / d));
  }
}

void unittest() {
  // gcd
  for (Int a = -100; a <= 100; ++a) for (Int b = -100; b <= 100; ++b) {
    Int g;
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
  for (Int n = 2; n < 100000; ++n) {
    bool composite = false;
    for (Int d = 2; d * d <= n; ++d) {
      composite = composite || (n % d == 0);
    }
    assert(isPrime(n) == !composite);
  }
  assert(isPrime(9223372036854775783LL));
  assert(!isPrime(7156857700403137441LL));

  // factorize
  assert(factorize(75600) == (vector<Int>{2, 2, 2, 2, 3, 3, 3, 5, 5, 7}));
  assert(factorize(4294967297LL) == (vector<Int>{641, 6700417}));
  assert(factorize(1000000016000000063LL) == (vector<Int>{1000000007, 1000000009}));
  assert(factorize(3141592653589793238LL) == (vector<Int>{2, 3, 11, 10513, 311743, 14523877}));
  assert(factorize(997748200186314745LL) == (vector<Int>{5, 7, 17, 17, 17581, 5610628223LL}));
}

// https://judge.yosupo.jp/problem/factorize
int main() {
  // unittest();

  int numCases;
  scanf("%d", &numCases);
  for (int caseId = 0; caseId < numCases; ++caseId) {
    Int n;
    scanf("%lld", &n);
    const auto res = factorize(n);
    printf("%d", static_cast<int>(res.size()));
    for (const Int p : res) {
      printf(" %lld", p);
    }
    puts("");
  }
  return 0;
}
