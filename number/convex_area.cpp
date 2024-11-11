#include <assert.h>
#include <math.h>
#include <utility>
#include <vector>
#include "../other/int128.h"

using std::pair;
using std::vector;

// \sum[1<=i<=N] floor(N/i)
__int128 Sigma0Brute(unsigned long long N) {
  const unsigned N2 = sqrt(static_cast<long double>(N));
  __int128 sum = 0;
  if (N2 + 1) {
    for (unsigned i = 1; i <= N2; ++i) sum += N / i;
  } else {
    for (unsigned i = 1; i; ++i) sum += N / i;
  }
  return 2 * sum - static_cast<unsigned long long>(N2) * N2;
}

// \sum[1<=i<=N] floor(N/i)
__int128 Sigma0(unsigned long long N) {
  if (N == 0) return 0;
  const unsigned long long N2 = sqrt(static_cast<long double>(N));
  unsigned long long N3 = cbrt(static_cast<long double>(N));
  for (; static_cast<unsigned __int128>(N3) * N3 * N3 < N; ++N3) {}
  for (; static_cast<unsigned __int128>(N3) * N3 * N3 > N; --N3) {}
  __int128 sum = 0;
  // \sum[1<=y<=floor(N^(1/2))] floor(N/y)
  using Pt = pair<unsigned long long, unsigned long long>;
  // { (x, y) | x y > N }: convex region
  auto inside = [&](unsigned long long x, unsigned long long y) -> bool {
    return (static_cast<unsigned __int128>(x) * y > N);
  };
  // -(slope at x) <= p.y/p.x
  auto steep = [&](unsigned long long x, const Pt &p) -> bool {
    return (static_cast<unsigned __int128>(N) * p.first <= static_cast<unsigned __int128>(p.second) * x * x);
  };
  vector<Pt> stack{{1, 0}, {1, 1}};
  // (x, y): inside
  unsigned long long x = N / N2, y = N2 + 1;
  for (; ; ) {
    Pt l = stack.back();
    stack.pop_back();
    for (; inside(x + l.first, y - l.second); x += l.first, y -= l.second) {
      // (x, y) -> (x + l.x, y - l.y)
      // sum for [y - l.y, y)
      sum += x * l.second + (l.first - 1) * (l.second + 1) / 2;
    }
    if (y <= N3) break;
    Pt r = l;
    for (; l = stack.back(), !inside(x + l.first, y - l.second); stack.pop_back()) r = l;
    // (x, y) + l: inside, (x, y) + r: outside
    for (; ; ) {
      const Pt m(l.first + r.first, l.second + r.second);
      if (inside(x + m.first, y - m.second)) {
        stack.push_back(l = m);
      } else {
        if (steep(x + m.first, l)) break;
        r = m;
      }
    }
  }
  for (; --y; ) sum += N / y;
  return 2 * sum - N2 * N2;
}

////////////////////////////////////////////////////////////////////////////////

#include <chrono>
#include <iostream>

using std::cerr;
using std::endl;

void unittest() {
  for (int n = 0; n <= 1'000; ++n) {
    assert(Sigma0Brute(n) == Sigma0(n));
  }
  // https://oeis.org/A085831
  assert(Sigma0Brute(~0ULL) == toInt128("821172508510810019729"));
  assert(Sigma0(~0ULL) == toInt128("821172508510810019729"));
}

void measure() {
  for (int E = 14; E <= 19; ++E) {
    unsigned long long N = 1;
    for (int e = 0; e < E; ++e) N *= 10;
    __int128 expected, actual;
    {
      const auto timerBegin = std::chrono::high_resolution_clock::now();
      expected = Sigma0Brute(N);
      const auto timerEnd = std::chrono::high_resolution_clock::now();
      cerr << "[Sigma0Brute] N = 10^" << E << ": expected = " << expected << "; "
           << std::chrono::duration_cast<std::chrono::milliseconds>(timerEnd - timerBegin).count() << " msec" << endl;
    }
    {
      const auto timerBegin = std::chrono::high_resolution_clock::now();
      actual = Sigma0(N);
      const auto timerEnd = std::chrono::high_resolution_clock::now();
      cerr << "[Sigma0]      N = 10^" << E << ": actual   = " << actual << "; "
           << std::chrono::duration_cast<std::chrono::milliseconds>(timerEnd - timerBegin).count() << " msec" << endl;
    }
    assert(expected == actual);
  }
}
/*
@AlRabbit
[Sigma0Brute] N = 10^14: expected = 3239062263181054; 24 msec
[Sigma0]      N = 10^14: actual   = 3239062263181054; 3 msec
[Sigma0Brute] N = 10^15: expected = 34693207724724246; 68 msec
[Sigma0]      N = 10^15: actual   = 34693207724724246; 7 msec
[Sigma0Brute] N = 10^16: expected = 369957928177109416; 208 msec
[Sigma0]      N = 10^16: actual   = 369957928177109416; 18 msec
[Sigma0Brute] N = 10^17: expected = 3929837791070240368; 669 msec
[Sigma0]      N = 10^17: actual   = 3929837791070240368; 49 msec
[Sigma0Brute] N = 10^18: expected = 41600963003695964400; 2110 msec
[Sigma0]      N = 10^18: actual   = 41600963003695964400; 91 msec
[Sigma0Brute] N = 10^19: expected = 439035480966899467508; 6673 msec
[Sigma0]      N = 10^19: actual   = 439035480966899467508; 208 msec
*/

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  measure(); cerr << "PASSED measure" << endl;
  return 0;
}
