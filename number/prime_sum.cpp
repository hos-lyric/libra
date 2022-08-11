#include <assert.h>
#include <math.h>
#include <algorithm>
#include <vector>

using std::min;
using std::vector;

// floor(a/b)
//   0 <= a <= 2^53
//   1 <= b <= 2^63 - 1
//   Proof (assuming IEEE 754):
//     Case. a = 0
//       OK
//     Case. 1 <= a <= 2^53 - 1:
//       floor(a/b) can be represented
//       take e \in \Z s.t. 2^e <= a/b < 2^(e+1)
//       1/b >= 2^e/a > 2^(e-53)
//       in [2^e, 2^(e+1)], the gaps between doubles are 2^(e-52)
//       (integer > floor(a/b)) > a/b + 2^(e-53) cannot be the nearest double
//     Case. a = 2^53:
//       the same argument applies when 2^e < a/b
//       OK when 2^e = a/b
inline long long div(long long a, int b) {
  return static_cast<double>(a) / b;
}
inline long long div(long long a, long long b) {
  return static_cast<double>(a) / b;
}

// \sum_{p<=n} f(p)  for floor(N/*)
//   f: completely multiplicative
//   g(p, n) := \sum_{1<=x<=n} [x: prime || lpf(x) > p] f(x)
//   for p: prime:
//     g(p, n) = | g(p-1, n)                                    (x <  p^2)
//               | g(p-1, n) - f(p) (g(p-1, n/p) - g(p-1, p-1))  (x >= p^2)
//   O(N^(3/4) / log N) time, O(N^(1/2)) space

struct PrimePi {
  long long N;
  int sqrtN;
  vector<int> small;
  vector<long long> large;
  explicit PrimePi(long long N_) : N(N_) {
    assert(0 <= N); assert(N <= 1LL << 53);
    sqrtN = sqrt(static_cast<double>(N));
    small.resize(sqrtN + 1);
    for (int k = 1; k <= sqrtN; ++k) small[k] = k;
    large.resize(sqrtN + 1);
    for (int l = 1; l <= sqrtN; ++l) large[l] = div(N, l);
    for (int p = 2; p <= sqrtN; ++p) if (small[p - 1] < small[p]) {
      const int g = small[p - 1];
      const int snp = sqrtN / p;
      const int psnp = p * snp;
      const long long np = div(N, p);
      const long long np2 = div(np, p);
      const int limL = min<long long>(np2, sqrtN);
      for (int l = 1; l <= snp; ++l) {
        large[l] -= (large[p * l] - g);
      }
      for (int l = snp + 1; l <= limL; ++l) {
        large[l] -= (small[div(np, l)] - g);
      }
      if (snp >= p) {
        for (int r = sqrtN - psnp; r >= 0; --r) {
          small[psnp + r] -= (small[snp] - g);
        }
        for (int k = snp; --k >= p; ) for (int r = p; --r >= 0; ) {
          small[p * k + r] -= (small[k] - g);
        }
      }
    }
    for (int k = 1; k <= sqrtN; ++k) --small[k];
    for (int l = 1; l <= sqrtN; ++l) --large[l];
  }
  // Assumes n = floor(N/*)
  inline long long operator()(long long n) const {
    return (n <= sqrtN) ? small[n] : large[div(N, n)];
  }
};

// TODO: general f(p)

// TODO: DFS

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <chrono>
#include <iostream>

using std::cerr;
using std::endl;

void unittest() {
  constexpr int LIM = 1'000'000;
  vector<bool> isPrime(LIM + 1, true);
  isPrime[0] = isPrime[1] = false;
  for (int p = 2; p <= LIM; ++p) if (isPrime[p]) {
    for (int n = 2 * p; n <= LIM; n += p) isPrime[n] = false;
  }
  vector<int> brt0(LIM + 1);
  brt0[0] = 0;
  for (int n = 1; n <= LIM; ++n) brt0[n] = brt0[n - 1] + (isPrime[n] ? 1 : 0);

  auto test = [&](int n) -> void {
    const PrimePi pi(n);
    for (int k = 1; k * k <= n; ++k) assert(brt0[k] == pi(k));
    for (int l = 1; l * l <= n; ++l) assert(brt0[n / l] == pi(n / l));
  };
  for (int n = 0; n <= 1'000; ++n) {
    test(n);
  }
  test(10'000);
  test(30'000);
  test(100'000);
  test(300'000);
  test(1'000'000);
}

void measurement(long long N, long long expected) {
  const auto timerBegin = std::chrono::high_resolution_clock::now();

  const PrimePi pi(N);
  const long long actual = pi(N);

  const auto timerEnd = std::chrono::high_resolution_clock::now();
  cerr << "[PrimePi] N = " << N << ": expected = " << expected
       << ", actual = " << actual << endl;
  cerr << std::chrono::duration_cast<std::chrono::milliseconds>(
      timerEnd - timerBegin).count() << " msec" << endl;
  assert(expected == actual);
}

// https://judge.yosupo.jp/problem/counting_primes
void yosupo__counting_primes() {
  long long N;
  for (; ~scanf("%lld", &N); ) {
    const PrimePi pi(N);
    printf("%lld\n", pi(N));
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  measurement(100'000'000'000LL, 4118054813LL);
  measurement(1'000'000'000'000LL, 37607912018LL);
  // yosupo__counting_primes();
  return 0;
}
