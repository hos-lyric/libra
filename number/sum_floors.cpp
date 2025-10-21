#include <assert.h>
#include <utility>

using std::swap;

template <class S> struct UnsignedOf;
template <> struct UnsignedOf<int> {
  using type = unsigned;
};
template <> struct UnsignedOf<long long> {
  using type = unsigned long long;
};
template <> struct UnsignedOf<__int128> {
  using type = unsigned __int128;
};

// \sum[0<=i<n] floor((ai+b)/m)
// U: unsigned integer,  (an+b) should not overflow
template <class T, class U> T sumFloorsUnsigned(U m, U a, U b, U n) {
  assert(m >= 1);
  T sum = 0;
  for (; ; ) {
    if (a >= m) {
      sum += ((n&1) ? (T(n) * T((n-1)/2)) : (T(n/2) * (T(n-1)))) * T(a / m);
      a %= m;
    }
    if (b >= m) {
      sum += T(n) * T(b / m);
      b %= m;
    }
    const U y = a * n + b;
    if (y < m) break;
    n = y / m;
    b = y % m;
    swap(m, a);
  }
  return sum;
}

// \sum[l<=i<r] floor((ai+b)/m)
// S: signed integer
// TODO: condition for overflow
template <class T, class S> T sumFloors(S m, S a, S b, S l, S r) {
  assert(m >= 1);
  assert(l <= r);
  const S n = r - l;
  b += a * l;
  T sum = 0;
  if (a < 0) {
    S q = a / m;
    if ((a %= m) < 0) { --q; a += m; }
    sum += ((n&1) ? (T(n) * T((n-1)/2)) : (T(n/2) * (T(n-1)))) * T(q);
  }
  if (b < 0) {
    S q = b / m;
    if ((b %= m) < 0) { --q; b += m; }
    sum += T(n) * T(q);
  }
  sum += sumFloorsUnsigned<T, typename UnsignedOf<S>::type>(m, a, b, r - l);
  return sum;
}

////////////////////////////////////////////////////////////////////////////////

#include <iostream>

using std::cerr;
using std::endl;

void unittest() {
  // sumFloorsUnsigned
  {
    constexpr unsigned LIM = 100;
    for (unsigned m = 1; m <= LIM; ++m) for (unsigned a = 0; a <= LIM; ++a) for (unsigned b = 0; b <= LIM; ++b) {
      unsigned brt = 0;
      for (unsigned n = 0; n <= LIM; ++n) {
        const unsigned res = sumFloorsUnsigned<unsigned, unsigned>(m, a, b, n);
        assert(brt == res);
        brt += (a * n + b) / m;
      }
    }
  }
  // sumFloors
  {
    constexpr int LIM = 25;
    for (int m = 1; m <= LIM; ++m) for (int a = -LIM; a <= LIM; ++a) for (int b = -LIM; b <= LIM; ++b) {
      for (int l = -LIM; l <= LIM; ++l) {
        int brt = 0;
        for (int r = l; r <= LIM; ++r) {
          const int res = sumFloors<int, int>(m, a, b, l, r);
          assert(brt == res);
          const int quo = (a * r + b) / m;
          const int rem = (a * r + b) % m;
          brt += (quo + ((rem < 0) ? -1 : 0));
        }
      }
    }
  }
}

// https://judge.yosupo.jp/problem/sum_of_floor_of_linear
void yosupo_sum_of_floor_of_linear() {
  int T;
  for (; ~scanf("%d", &T); ) {
    for (int t = 0; t < T; ++t) {
      unsigned long long N, M, A, B;
      scanf("%llu%llu%llu%llu", &N, &M, &A, &B);
      const unsigned long long ans = sumFloorsUnsigned<unsigned long long>(M, A, B, N);
      printf("%llu\n", ans);
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  // yosupo_sum_of_floor_of_linear();
  return 0;
}
