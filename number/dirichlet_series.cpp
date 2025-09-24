#include <assert.h>
#include <math.h>
#include <sstream>
#include <vector>

using std::vector;

// TODO: O~(N^(2/3))

// quo[i - 1] < x <= quo[i] <=> floor(N/x) = quo[len - i]  (1 <= i <= len - 1)
struct Quotients {
  long long N;
  int N2, N3, N4, N6;
  int len;
  explicit Quotients(long long N_ = 0) : N(N_) {
    N2 = sqrt(static_cast<long double>(N));
    N3 = cbrt(static_cast<long double>(N));
    for (; static_cast<long long>(N3) * N3 * N3 < N; ++N3) {}
    for (; static_cast<long long>(N3) * N3 * N3 > N; --N3) {}
    N4 = sqrt(static_cast<long double>(N2));
    N6 = sqrt(static_cast<long double>(N3));
    len = 2 * N2 + ((static_cast<long long>(N2) * (N2 + 1) <= N) ? 1 : 0);
  }
  long long operator[](int i) const {
    return (i <= N2) ? i : (N / (len - i));
  }
  int indexOf(long long x) const {
    return (x <= N2) ? x : (len - (N / x));
  }
  friend std::ostream &operator<<(std::ostream &os, const Quotients &quo) {
    os << "[";
    for (int i = 0; i < quo.len; ++i) {
      if (i) os << ", ";
      os << quo[i];
    }
    os << "]";
    return os;
  }
};

template <class T> struct Dirichlet {
  Quotients quo;
  vector<T> ts;
  explicit Dirichlet(long long N_ = 0) : quo(N_), ts(quo.len) {}
  T operator[](int i) const { return ts[i]; }
  T &operator[](int i) { return ts[i]; }
  T operator()(long long x) const { return ts[quo.indexOf(x)]; }
  T &operator()(long long x) { return ts[quo.indexOf(x)]; }
  T point(int i) const { return ts[i] - ts[i - 1]; }
  friend std::ostream &operator<<(std::ostream &os, const Dirichlet &A) {
    os << "[";
    for (int i = 0; i < A.quo.len; ++i) {
      if (i) os << ", ";
      os << A.quo[i] << ":" << A.ts[i];
    }
    os << "]";
    return os;
  }

  Dirichlet &operator+=(const Dirichlet &A) {
    assert(quo.N == A.quo.N);
    for (int i = 0; i < quo.len; ++i) ts[i] += A.ts[i];
    return *this;
  }
  Dirichlet &operator-=(const Dirichlet &A) {
    assert(quo.N == A.quo.N);
    for (int i = 0; i < quo.len; ++i) ts[i] -= A.ts[i];
    return *this;
  }
  Dirichlet &operator*=(const T &t) {
    for (int i = 0; i < quo.len; ++i) ts[i] *= t;
    return *this;
  }
  Dirichlet operator+() const {
    return *this;
  }
  Dirichlet operator-() const {
    Dirichlet A(quo.N);
    for (int i = 0; i < quo.len; ++i) A.ts[i] = -ts[i];
    return A;
  }
  Dirichlet operator+(const Dirichlet &A) const { return Dirichlet(*this) += A; }
  Dirichlet operator-(const Dirichlet &A) const { return Dirichlet(*this) -= A; }
  Dirichlet operator*(const T &t) const { return Dirichlet(*this) *= t; }
  friend Dirichlet operator*(const T &t, const Dirichlet &A) { return A * t; }

  // Assumes a: completely multiplicative.
  // a(n) *= [n: prime]
  // O(N^(3/4) log(N)^-1) time (O(N^(3/4)) if broken)
  // for p: prime <= N^(1/2) (incr.):
  //   for p^2 <= n <= N (decr.):
  //     A(n) -= a(p) (A(n/p) - A(p-1))
  void primeSum() {
    vector<int> isPrime(quo.N2 + 1, 1);
    isPrime[0] = isPrime[1] = 0;
    for (int p = 2; p <= quo.N2; ++p) if (isPrime[p]) {
      for (int n = 2 * p; n <= quo.N2; n += p) isPrime[n] = 0;
    }
    Dirichlet &A = *this;
    for (int p = 2; p <= quo.N2; ++p) if (isPrime[p]) {
      const T ap = A.point(p);
      if (ap) {
        const long long p2 = static_cast<long long>(p) * p;
        for (int i = quo.len; quo[--i] >= p2; ) {
          A[i] -= ap * (A(quo[i] / p) - A[p - 1]);
        }
      }
    }
    for (int i = 1; i < quo.len; ++i) A[i] -= 1;
  }

  // Assumes a(n) = [n: prime] f(n).
  // Makes a to be multiplicative, a(p^e) = f(p^e).
  //   f(p, e, p^e) (e >= 2) should return f(p^e).
  // O(N^(3/4) log(N)^-1) time
  // for p: prime <= N^(1/2) (decr.):
  //   for p^2 <= n <= N (decr.):
  //     A(n) += \sum[e>=1,p^(e+1)<=n] (f(p^e) (A(n/p) - A(p)) + f(p^(e+1)))
  template <class F> void multiplicativeSum(F f) {
    vector<int> isPrime(quo.N2 + 1, 1);
    isPrime[0] = isPrime[1] = 0;
    for (int p = 2; p <= quo.N2; ++p) if (isPrime[p]) {
      for (int n = 2 * p; n <= quo.N2; n += p) isPrime[n] = 0;
    }
    Dirichlet &A = *this;
    for (int i = 1; i < quo.len; ++i) A[i] += 1;
    for (int p = quo.N2; p >= 2; --p) if (isPrime[p]) {
      vector<long long> pps{1, p};
      vector<T> fs{1, A.point(p)};
      for (int e = 2; pps.back() <= quo.N / p; ++e) {
        pps.push_back(pps.back() * p);
        fs.push_back(f(p, e, pps.back()));
      }
      for (int i = quo.len; quo[--i] >= pps[2]; ) {
        long long nn = quo[i];
        for (int e = 1; (nn /= p) >= p; ++e) {
          A[i] += fs[e] * (A(nn) - A[p]) + fs[e + 1];
        }
      }
    }
  }

  // a(n) = n^k
  Dirichlet Id(int k) const;
  // a(n) = [n: prime] n^k
  Dirichlet IdPrime(int k) const;
  // a(p) = \sum[k] coefs[k] p^k
  // a(p^e) = f(p, e, p^e)  (e >= 2)
  template <class F>
  Dirichlet IdMultiplicative(const vector<T> &coefs, F f) const;
};

template <class T> T powerSum(int k, long long n) {
  if (k == 0) {
    return T(n);
  } else if (k == 1) {
    long long ns[2] = {n, n + 1};
    ns[n % 2] /= 2;
    return T(ns[0]) * T(ns[1]);
  } else if (k == 2) {
    long long ns[3] = {n, 2 * n + 1, n + 1};
    ns[n % 2 * 2] /= 2;
    ns[n % 3] /= 3;
    return T(ns[0]) * T(ns[1]) * T(ns[2]);
  } else if (k == 3) {
    const T t = powerSum<T>(1, n);
    return t * t;
  } else if (k == 4) {
    long long ns[5] = {n, n - 1, 2 * n + 1, n + 2, n + 1};
    ns[n % 2] /= 2;
    ns[n % 5] /= 5;
    return T(ns[0]) * T(ns[1]) * T(ns[2]) * T(ns[3]) * T(ns[4]) + powerSum<T>(2, n);
  } else if (k == 5) {
    long long ns[3] = {n, n - 1, n + 1};
    ns[n % 2] /= 2;
    ns[n % 3] /= 3;
    return T(ns[0]) * T(ns[1]) * T(ns[2]) * T(n) * T(n + 1) * T(n + 2) + powerSum<T>(3, n);
  } else {
    assert(false);
  }
}
template <class T> Dirichlet<T> Id(int k, long long N) {
  Dirichlet<T> A(N);
  const Quotients quo = A.quo;
  for (int n = 1; n <= quo.N2; ++n) {
    T t = 1;
    for (int j = 0; j < k; ++j) t *= n;
    A[n] = A[n - 1] + t;
  }
  for (int i = quo.N2 + 1; i < quo.len; ++i) A[i] = powerSum<T>(k, quo[i]);
  return A;
}
template <class T> Dirichlet<T> IdPrime(int k, long long N) {
  auto A = Id<T>(k, N);
  A.primeSum();
  return A;
}
template <class T, class F>
Dirichlet<T> IdMultiplicative(const vector<T> &coefs, F f, long long N) {
  Dirichlet<T> A(N);
  for (int k = 0; k < static_cast<int>(coefs.size()); ++k) if (coefs[k]) {
    A += coefs[k] * A.IdPrime(k);
  }
  A.multiplicativeSum(f);
  return A;
}

template <class T> Dirichlet<T> Dirichlet<T>::Id(int k) const {
  return ::Id<T>(k, quo.N);
}
template <class T> Dirichlet<T> Dirichlet<T>::IdPrime(int k) const {
  return ::IdPrime<T>(k, quo.N);
}
template <class T> template <class F>
Dirichlet<T> Dirichlet<T>::IdMultiplicative(const vector<T> &coefs, F f) const {
  return ::IdMultiplicative<T>(coefs, f, quo.N);
}

////////////////////////////////////////////////////////////////////////////////

#include <algorithm>
#include <chrono>
#include <iostream>

using std::cerr;
using std::endl;

void unittest_Quotients() {
  {
    Quotients quo;
    quo = Quotients(19);
    std::ostringstream oss;
    oss << quo;
    assert(oss.str() == "[0, 1, 2, 3, 4, 6, 9, 19]");
  }
  {
    Quotients quo;
    quo = Quotients(24);
    std::ostringstream oss;
    oss << quo;
    assert(oss.str() == "[0, 1, 2, 3, 4, 6, 8, 12, 24]");
  }
  for (int N = 0; N <= 1'000; ++N) {
    vector<int> xs;
    xs.push_back(0);
    for (int y = 1; y <= N; ++y) xs.push_back(N / y);
    std::sort(xs.begin(), xs.end());
    xs.erase(std::unique(xs.begin(), xs.end()), xs.end());
    const int len = xs.size();
    const Quotients quo(N);
    assert(quo.len == len);
    for (int i = 0; i < len; ++i) assert(quo[i] == xs[i]);
    for (int i = 1; i < len; ++i) {
      for (int x = xs[i - 1] + 1; x <= xs[i]; ++x) assert(quo.indexOf(x) == i);
    }
  }
}

void unittest_primeSum() {
  {
    const auto A = IdPrime<int>(0, 19);
    std::ostringstream oss;
    oss << A;
    assert(oss.str() == "[0:0, 1:0, 2:1, 3:2, 4:2, 6:3, 9:4, 19:8]");
  }
  {
    const auto A = IdPrime<int>(1, 24);
    std::ostringstream oss;
    oss << A;
    assert(oss.str() == "[0:0, 1:0, 2:2, 3:5, 4:5, 6:10, 8:17, 12:28, 24:100]");
  }
  for (int k = 0; k <= 5; ++k) {
    constexpr int MAX_N = 1'000;
    vector<unsigned long long> as(MAX_N + 1, 0), bs(MAX_N + 1, 0);
    for (int n = 1; n <= MAX_N; ++n) {
      as[n] = 1;
      for (int j = 0; j < k; ++j) as[n] *= n;
      bool isPrime = (n >= 2);
      for (int p = 2; p * p <= n; ++p) if (n % p == 0) {
        isPrime = false;
        break;
      }
      if (isPrime) bs[n] = as[n];
      as[n] += as[n - 1];
      bs[n] += bs[n - 1];
    }
    for (int N = 1; N <= MAX_N; ++N) {
      auto A = Id<unsigned long long>(k, N);
      for (int i = 0; i < A.quo.len; ++i) assert(A[i] == as[A.quo[i]]);
      A.primeSum();
      for (int i = 0; i < A.quo.len; ++i) assert(A[i] == bs[A.quo[i]]);
    }
  }
}

void unittest_multiplicativeSum() {
  // mu
  {
    auto A = -IdPrime<int>(0, 19);
    A.multiplicativeSum([&](int /*p*/, int /*e*/, long long /*pp*/) -> int {
      return 0;
    });
    std::ostringstream oss;
    oss << A;
    assert(oss.str() == "[0:0, 1:1, 2:0, 3:-1, 4:-1, 6:-1, 9:-2, 19:-3]");
  }
  // phi
  {
    const auto A = IdMultiplicative<int>(
      {-1, 1},
      [&](int p, int /*e*/, long long pp) -> int {
        return pp / p * (p - 1);
      },
      24
    );
    std::ostringstream oss;
    oss << A;
    assert(oss.str() == "[0:0, 1:1, 2:2, 3:4, 4:6, 6:12, 8:22, 12:46, 24:180]");
  }
  // sigma_k
  for (int k = 0; k <= 5; ++k) {
    constexpr int MAX_N = 1'000;
    vector<unsigned long long> as(MAX_N + 1, 0);
    for (int d = 1; d <= MAX_N; ++d) {
      unsigned long long dk = 1;
      for (int j = 0; j < k; ++j) dk *= d;
      for (int n = d; n <= MAX_N; n += d) as[n] += dk;
    }
    for (int n = 1; n <= MAX_N; ++n) as[n] += as[n - 1];
    for (int N = 1; N <= MAX_N; ++N) {
      Dirichlet<unsigned long long> A(N);
      A += A.IdPrime(0);
      A += A.IdPrime(k);
      A.multiplicativeSum([&](int p, int e, long long /*pp*/) -> unsigned long long {
        assert(e >= 2);
        unsigned long long sum = 1, ppk = 1;
        for (int f = 1; f <= e; ++f) {
          for (int j = 0; j < k; ++j) ppk *= p;
          sum += ppk;
        }
        return sum;
      });
      for (int i = 0; i < A.quo.len; ++i) assert(A[i] == as[A.quo[i]]);
    }
  }
}

void measure_primeSum() {
  // isPrime
  // https://oeis.org/A006880
  constexpr long long EXPECTED[] = {0, 4, 25, 168, 1229, 9592, 78498, 664579, 5761455, 50847534, 455052511, 4118054813, 37607912018, 346065536839, 3204941750802, 29844570422669, 279238341033925, 2623557157654233, 24739954287740860};
  long long N = 1;
  for (int e = 0; e <= 12; ++e, N *= 10) {
    const auto timerBegin = std::chrono::high_resolution_clock::now();
    const auto A = IdPrime<long long>(0, N);
    const auto timerEnd = std::chrono::high_resolution_clock::now();
    cerr << "pi(10^" << e << ") = " << A(N) << "; "
         << std::chrono::duration_cast<std::chrono::milliseconds>(timerEnd - timerBegin).count()
         << " msec" << endl;
    assert(A(N) == EXPECTED[e]);
  }
}

void measure_multiplicativeSum() {
  // mu
  // https://oeis.org/A084237
  constexpr long long EXPECTED[] = {1, -1, 1, 2, -23, -48, 212, 1037, 1928, -222, -33722, -87856, 62366, 599582, -875575, -3216373, -3195437, -21830254, -46758740};
  long long N = 1;
  for (int e = 0; e <= 12; ++e, N *= 10) {
    auto A = -IdPrime<long long>(0, N);
    const auto timerBegin = std::chrono::high_resolution_clock::now();
    A.multiplicativeSum([&](int /*p*/, int /*e*/, long long /*pp*/) -> int {
      return 0;
    });
    const auto timerEnd = std::chrono::high_resolution_clock::now();
    cerr << "Mu(10^" << e << ") = " << A(N) << "; "
         << std::chrono::duration_cast<std::chrono::milliseconds>(timerEnd - timerBegin).count()
         << " msec" << endl;
    assert(A(N) == EXPECTED[e]);
  }
}

int main() {
  unittest_Quotients(); cerr << "PASSED unittest_Quotients" << endl;
  unittest_primeSum(); cerr << "PASSED unittest_primeSum" << endl;
  unittest_multiplicativeSum(); cerr << "PASSED unittest_multiplicativeSum" << endl;
  measure_primeSum();
  measure_multiplicativeSum();
  return 0;
}
