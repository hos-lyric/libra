#include <assert.h>
#include <math.h>
#include <algorithm>
#include <vector>

using std::min;
using std::vector;

// floor(a/b)  by double
//   0 <= a <= 2^53
//   1 <= b <= 2^53
//   Proof (assuming IEEE 754):
//     a, b, floor(a/b): representable
//     Case. a = 0
//       OK
//     Case. 1 <= a <= 2^53 - 1:
//       take e s.t. 2^e <= a/b < 2^(e+1)  (0 <= e <= 52)
//       in [2^e, 2^(e+1)], the gaps between doubles are 2^(e-52)
//       (floor(a/b) + 1) - a/b >= 1/b >= 2^e/a > 2^(e-53)
//       therefore (the nearest double to a/b) < floor(a/b) + 1
//     Case. a = 2^53:
//       the same argument applies when 2^e < a/b
//       OK when 2^e = a/b

// floor(sqrt(n))  by double
//   0 <= n <= (2^26 + 1)^2 - 2
//   Proof (assuming IEEE 754):
//     n, floor(sqrt(n)): representable
//     Case. n = 0:
//       OK
//     Case. 1 <= n <= 2^52 - 1:
//       m := floor(sqrt(n))
//       take e s.t. 2^e <= m < 2^(e+1)  (0 <= e <= 25)
//       in [2^e, 2^(e+1)], the gaps between doubles are 2^(e-52)
//       (m + 1) - sqrt(n) >= (m+1) - sqrt((m+1)^2-1)
//                         >= 1 / (2(m+1)) >= 2^(-e-2) > 2^(e-53)
//       therefore (the nearest double to sqrt(n)) < m + 1
//     Case. 2^52 <= n <= (2^26 + 1)^2 - 2:
//       floor(sqrt(n)) = 2^26
//       OK

// \sum_{p<=n} f(p)  for n = floor(N/*)
//   f: completely multiplicative
//   g(p, n) := \sum[1<=x<=n] [x: prime || lpf(x) > p] f(x)
//   g(1, n) = \sum[1<=x<=n] f(x)  (need to be computed quickly)
//   for p: prime:
//     g(p, n) = | g(p-1, n)                                     (n <  p^2)
//               | g(p-1, n) - f(p) (g(p-1, n/p) - g(p-1, p-1))  (n >= p^2)
//   O(N^(3/4) / log(N)) time, O(N^(1/2)) space

inline long long divide(long long a, int b) {
  return static_cast<double>(a) / b;
}
inline long long divide(long long a, long long b) {
  return static_cast<double>(a) / b;
}
struct PrimePi {
  long long N;
  int sqrtN;
  vector<int> small;
  vector<long long> large;
  int primesLen;
  vector<int> primes;
  PrimePi() {}
  explicit PrimePi(long long N_) : N(N_) {
    assert(0 <= N); assert(N <= 1LL << 52);
    sqrtN = sqrt(static_cast<double>(N));
    small.assign(sqrtN + 1, 0);
    for (int k = 1; k <= sqrtN; ++k) small[k] = k;
    large.assign(sqrtN + 1, 0);
    for (int l = 1; l <= sqrtN; ++l) large[l] = divide(N, l);
    for (int p = 2; p <= sqrtN; ++p) if (small[p - 1] < small[p]) {
      const int g = small[p - 1];
      const int snp = sqrtN / p;
      const int psnp = p * snp;
      const long long np = divide(N, p);
      const int limL = min<long long>(divide(np, p), sqrtN);
      for (int l = 1; l <= snp; ++l) {
        large[l] -= (large[p * l] - g);
      }
      for (int l = snp + 1; l <= limL; ++l) {
        large[l] -= (small[divide(np, l)] - g);
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
    primesLen = small[sqrtN];
    primes.resize(primesLen);
    for (int p = 2; p <= sqrtN; ++p) if (small[p - 1] < small[p]) {
      primes[small[p - 1]] = p;
    }
  }
  // Assumes n = floor(N/*)
  inline long long operator()(long long n) const {
    return (n <= sqrtN) ? small[n] : large[divide(N, n)];
  }
};

// TODO: general f(p)

////////////////////////////////////////////////////////////////////////////////

// \sum_{1<=n<=N} 1
namespace gpf_tree_1 {
PrimePi pi;
long long ans;
void dfs(int i, long long n) {
  {
    // n p  (primes[i] <= p <= N/n)
    ans += (pi(divide(pi.N, n)) - i);
  }
  for (; i < pi.primesLen; ++i) {
    const int p = pi.primes[i];
    long long npe = n * p;
    for (int e = 1; ; ++e) {
      const long long npep = npe * p;
      if (npep > pi.N) {
        if (e == 1) return;
        break;
      }
      {
        // n -> n p^e
        dfs(i + 1, npe);
      }
      {
        // n p^(e+1)
        ans += 1;
      }
      npe = npep;
    }
  }
}
long long run(long long N) {
  pi = PrimePi(N);
  ans = 0;
  if (1 <= N) {
    // 1
    ans += 1;
  }
  dfs(0, 1);
  return ans;
}
}  // namespace gpf_tree_1

////////////////////////////////////////////////////////////////////////////////

// \sum_{1<=n<=N} \omega(n)
namespace gpf_tree_omega {
PrimePi pi;
long long ans;
void dfs(int i, long long n, int sumE) {
  {
    // n p  (primes[i] <= p <= N/n)
    ans += (pi(divide(pi.N, n)) - i) * (sumE + 1);
  }
  for (; i < pi.primesLen; ++i) {
    const int p = pi.primes[i];
    long long npe = n * p;
    for (int e = 1; ; ++e) {
      const long long npep = npe * p;
      if (npep > pi.N) {
        if (e == 1) return;
        break;
      }
      {
        // n -> n p^e
        dfs(i + 1, npe, sumE + e);
      }
      {
        // n p^(e+1)
        ans += (sumE + (e + 1));
      }
      npe = npep;
    }
  }
}
long long run(long long N) {
  pi = PrimePi(N);
  ans = 0;
  if (1 <= N) {
    // 1
    ans += 0;
  }
  dfs(0, 1, 0);
  return ans;
}
}  // namespace gpf_tree_omega

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

  for (int n = 0; n <= 4; ++n) {
    assert(gpf_tree_1::run(n) == n);
  }
  for (long long n = 10; n <= 10'000'000'000LL; n *= 10) {
    assert(gpf_tree_1::run(n) == n);
  }
}

void measurement_PrimePi(long long N, long long expected) {
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

void measurement_gpf_tree_1(long long N) {
  const long long expected = N;
  const auto timerBegin = std::chrono::high_resolution_clock::now();

  const long long actual = gpf_tree_1::run(N);

  const auto timerEnd = std::chrono::high_resolution_clock::now();
  cerr << "[gpf_tree_1] N = " << N << ": expected = " << expected
       << ", actual = " << actual << endl;
  cerr << std::chrono::duration_cast<std::chrono::milliseconds>(
      timerEnd - timerBegin).count() << " msec" << endl;
  assert(expected == actual);
}

// https://judge.yosupo.jp/problem/counting_primes
void yosupo_counting_primes() {
  long long N;
  for (; ~scanf("%lld", &N); ) {
    const PrimePi pi(N);
    printf("%lld\n", pi(N));
  }
}

// https://atcoder.jp/contests/xmascon19/tasks/xmascon19_e
void atcoder_xmascon19_e() {
  long long N;
  for (; ~scanf("%lld", &N); ) {
    const long long ans = gpf_tree_omega::run(N);
    printf("%lld\n", ans);
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  measurement_PrimePi(100'000'000'000LL, 4118054813LL);
  measurement_PrimePi(1'000'000'000'000LL, 37607912018LL);
  measurement_gpf_tree_1(100'000'000'000LL);
  measurement_gpf_tree_1(1'000'000'000'000LL);
  // yosupo_counting_primes();
  // atcoder_xmascon19_e();
  return 0;
}
