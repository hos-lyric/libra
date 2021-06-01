#include <assert.h>
#include <string.h>
#include <algorithm>
#include <vector>

using std::max;
using std::min;
using std::vector;

////////////////////////////////////////////////////////////////////////////////
namespace radix3 {

constexpr int THREE[20] = {1, 3, 9, 27, 81, 243, 729, 2187, 6561, 19683, 59049, 177147, 531441, 1594323, 4782969, 14348907, 43046721, 129140163, 387420489, 1162261467};

template <class R> inline void div3(R &a);

template <int Q, class R> inline void zero(R *as) {
  memset(as, 0, (2 * THREE[Q]) * sizeof(R));
}
template <int Q, class R> inline void cpy(R *as, R *bs) {
  memcpy(as, bs, (2 * THREE[Q]) * sizeof(R));
}
template <int Q, class R> inline void add(R *as, R *bs) {
  for (int j = 0; j < 2 * THREE[Q]; ++j) as[j] += bs[j];
}
template <int Q, class R> inline void add2(R *as, R *bs) {
  for (int j = 0; j < 2 * THREE[Q]; ++j) as[j] += 2 * bs[j];
}
template <int Q, class R> inline void mulAdd(R *as, R *bs, int r) {
  if (r >= THREE[Q + 1]) r -= THREE[Q + 1];
  const int j2 = max(2 * THREE[Q] - r, 0);
  const int j3 = min(THREE[Q + 1] - r, 2 * THREE[Q]);
  for (int j = 0; j < j2; ++j) as[j + r] += bs[j];
  for (int j = j2; j < j3; ++j) { as[j + r - 2 * THREE[Q]] -= bs[j]; as[j + r - THREE[Q]] -= bs[j]; }
  for (int j = j3; j < 2 * THREE[Q]; ++j) as[j + r - THREE[Q + 1]] += bs[j];
}
template <int Q, class R> inline void mulAdd2(R *as, R *bs, int r) {
  if (r >= THREE[Q + 1]) r -= THREE[Q + 1];
  const int j2 = max(2 * THREE[Q] - r, 0);
  const int j3 = min(THREE[Q + 1] - r, 2 * THREE[Q]);
  for (int j = 0; j < j2; ++j) as[j + r] += 2 * bs[j];
  for (int j = j2; j < j3; ++j) { as[j + r - 2 * THREE[Q]] -= 2 * bs[j]; as[j + r - THREE[Q]] -= 2 * bs[j]; }
  for (int j = j3; j < 2 * THREE[Q]; ++j) as[j + r - THREE[Q + 1]] += 2 * bs[j];
}
template <int Q, class R> inline void mulSub(R *as, R *bs, int r) {
  if (r >= THREE[Q + 1]) r -= THREE[Q + 1];
  const int j2 = max(2 * THREE[Q] - r, 0);
  const int j3 = min(THREE[Q + 1] - r, 2 * THREE[Q]);
  for (int j = 0; j < j2; ++j) as[j + r] -= bs[j];
  for (int j = j2; j < j3; ++j) { as[j + r - 2 * THREE[Q]] += bs[j]; as[j + r - THREE[Q]] += bs[j]; }
  for (int j = j3; j < 2 * THREE[Q]; ++j) as[j + r - THREE[Q + 1]] -= bs[j];
}
template <int Q, class R> inline void mulSub2(R *as, R *bs, int r) {
  if (r >= THREE[Q + 1]) r -= THREE[Q + 1];
  const int j2 = max(2 * THREE[Q] - r, 0);
  const int j3 = min(THREE[Q + 1] - r, 2 * THREE[Q]);
  for (int j = 0; j < j2; ++j) as[j + r] -= 2 * bs[j];
  for (int j = j2; j < j3; ++j) { as[j + r - 2 * THREE[Q]] += 2 * bs[j]; as[j + r - THREE[Q]] += 2 * bs[j]; }
  for (int j = j3; j < 2 * THREE[Q]; ++j) as[j + r - THREE[Q + 1]] -= 2 * bs[j];
}

// DFT of size 3^p over R[y] / (1 + y^(3^q) + y^(2 3^q))
template <int M, class R> void fft(R *as) {
  static constexpr int P = M / 2, Q = M - M / 2;
  static R ratios[P] = {};
  for (int g = 0; g < P - 1; ++g) ratios[g] = (2 * THREE[Q] + 4 * THREE[Q - g - 1]) % THREE[Q + 1];
  static R work1[2 * THREE[Q]], work2[2 * THREE[Q]];
  for (int l = P; --l >= 0; ) {
    int prod = 0;
    for (int h = 0, i0 = 0; i0 < THREE[P]; i0 += THREE[l + 1]) {
      for (int i = i0; i < i0 + THREE[l]; ++i) {
        R *a0 = as + 2 * THREE[Q] * i;
        R *a1 = as + 2 * THREE[Q] * (i + THREE[l]);
        R *a2 = as + 2 * THREE[Q] * (i + 2 * THREE[l]);
        zero<Q>(work1);
        mulAdd<Q>(work1, a1, prod);
        zero<Q>(work2);
        mulAdd<Q>(work2, a2, 2 * prod);
        cpy<Q>(a1, a0);
        mulAdd<Q>(a1, work1, THREE[Q]);
        mulAdd<Q>(a1, work2, 2 * THREE[Q]);
        cpy<Q>(a2, a0);
        mulAdd<Q>(a2, work1, 2 * THREE[Q]);
        mulAdd<Q>(a2, work2, THREE[Q]);
        add<Q>(a0, work1);
        add<Q>(a0, work2);
      }
      int g = 0;
      for (int hh = ++h; hh % 3 == 0; hh /= 3) ++g;
      if ((prod += ratios[g]) >= THREE[Q + 1]) prod -= THREE[Q + 1];
    }
  }
}

// inverse DFT of size 3^p over R[y] / (1 + y^(3^q) + y^(2 3^q))
template <int M, class R> void invFft(R *as) {
  static constexpr int P = M / 2, Q = M - M / 2;
  static R invRatios[P] = {};
  for (int g = 0; g < P - 1; ++g) invRatios[g] = (4 * THREE[Q] - 4 * THREE[Q - g - 1]) % THREE[Q + 1];
  static R work1[2 * THREE[Q]], work2[2 * THREE[Q]];
  for (int l = 0; l < P; ++l) {
    int prod = 0;
    for (int h = 0, i0 = 0; i0 < THREE[P]; i0 += THREE[l + 1]) {
      for (int i = i0; i < i0 + THREE[l]; ++i) {
        R *a0 = as + 2 * THREE[Q] * i;
        R *a1 = as + 2 * THREE[Q] * (i + THREE[l]);
        R *a2 = as + 2 * THREE[Q] * (i + 2 * THREE[l]);
        cpy<Q>(work1, a0);
        mulAdd<Q>(work1, a1, 2 * THREE[Q]);
        mulAdd<Q>(work1, a2, THREE[Q]);
        cpy<Q>(work2, a0);
        mulAdd<Q>(work2, a1, THREE[Q]);
        mulAdd<Q>(work2, a2, 2 * THREE[Q]);
        add<Q>(a0, a1);
        add<Q>(a0, a2);
        zero<Q>(a1);
        mulAdd<Q>(a1, work1, prod);
        zero<Q>(a2);
        mulAdd<Q>(a2, work2, 2 * prod);
      }
      int g = 0;
      for (int hh = ++h; hh % 3 == 0; hh /= 3) ++g;
      if ((prod += invRatios[g]) >= THREE[Q + 1]) prod -= THREE[Q + 1];
    }
  }
  R inv3 = 1;
  for (int l = 0; l < P; ++l) div3(inv3);
  for (int k = 0; k < 2 * THREE[M]; ++k) as[k] *= inv3;
}

// a <- a b mod (1 + x^(3^m) + x^(2 3^m))
template <int M, class R> void inplaceConvolve(R *as, R *bs) {
  if (M <= 3) {
    static R cs[4 * THREE[M] - 1];
    memset(cs, 0, (4 * THREE[M] - 1) * sizeof(R));
    for (int ka = 0; ka < 2 * THREE[M]; ++ka) for (int kb = 0; kb < 2 * THREE[M]; ++kb) cs[ka + kb] += as[ka] * bs[kb];
    for (int k = 4 * THREE[M] - 1; --k >= 2 * THREE[M]; ) {
      cs[k - 2 * THREE[M]] -= cs[k];
      cs[k - THREE[M]] -= cs[k];
    }
    memcpy(as, cs, (2 * THREE[M]) * sizeof(R));
  } else {
    // y := x^(3^p)
    // (R[y] / (1 + y^(3^q) + y^(2 3^q)))[x]
    static constexpr int P = M / 2, Q = M - M / 2;
    static R as0[2 * THREE[M]], bs0[2 * THREE[M]], as1[2 * THREE[M]], bs1[2 * THREE[M]];
    for (int j = 0; j < 2 * THREE[Q]; ++j) for (int i = 0; i < THREE[P]; ++i) as0[2 * THREE[Q] * i + j] = as[THREE[P] * j + i];
    for (int j = 0; j < 2 * THREE[Q]; ++j) for (int i = 0; i < THREE[P]; ++i) bs0[2 * THREE[Q] * i + j] = bs[THREE[P] * j + i];
    // x <- y^(3^q/3^p) x
    zero<M>(as1);
    zero<M>(bs1);
    for (int i = 0; i < THREE[P]; ++i) mulAdd<Q>(as1 + 2 * THREE[Q] * i, as0 + 2 * THREE[Q] * i, THREE[Q - P] * i);
    for (int i = 0; i < THREE[P]; ++i) mulAdd<Q>(bs1 + 2 * THREE[Q] * i, bs0 + 2 * THREE[Q] * i, THREE[Q - P] * i);
    fft<M>(as0);
    fft<M>(bs0);
    for (int i = 0; i < THREE[P]; ++i) inplaceConvolve<Q>(bs0 + 2 * THREE[Q] * i, as0 + 2 * THREE[Q] * i);
    invFft<M>(bs0);
    fft<M>(as1);
    fft<M>(bs1);
    for (int i = 0; i < THREE[P]; ++i) inplaceConvolve<Q>(bs1 + 2 * THREE[Q] * i, as1 + 2 * THREE[Q] * i);
    invFft<M>(bs1);
    zero<M>(as);
    for (int i = 0; i < THREE[P]; ++i) {
      // b0 = c0 + c1
      // b1 = y^(3^q/3^p i) c0 + y^(3^q/3^p i + 3^q) c1
      // c0 = (1/3) (2 + y^(3^q)) (-y^(3^q) b0 + y^(-3^q/3^p i) b1)
      // c1 = (1/3) (2 + y^(3^q)) (b0 - y^(-3^q/3^p i) b1)
      R *b0 = bs0 + 2 * THREE[Q] * i;
      R *b1 = bs1 + 2 * THREE[Q] * i;
      for (int j = 0; j < 2 * THREE[Q]; ++j) div3(b0[j]);
      for (int j = 0; j < 2 * THREE[Q]; ++j) div3(b1[j]);
      zero<Q>(as0);
      mulSub2<Q>(as0, b0, THREE[Q]);
      mulSub<Q>(as0, b0, 2 * THREE[Q]);
      mulAdd2<Q>(as0, b1, THREE[Q + 1] - THREE[Q - P] * i);
      mulAdd<Q>(as0, b1, THREE[Q + 1] - THREE[Q - P] * i + THREE[Q]);
      zero<Q>(as1);
      add2<Q>(as1, b0);
      mulAdd<Q>(as1, b0, THREE[Q]);
      mulSub2<Q>(as1, b1, THREE[Q + 1] - THREE[Q - P] * i);
      mulSub<Q>(as1, b1, THREE[Q + 1] - THREE[Q - P] * i + THREE[Q]);
      for (int j = 0; j < 2 * THREE[Q]; ++j) as[THREE[P] * j + i] += as0[j];
      for (int j = 0; j < 2 * THREE[Q] - 1; ++j) as[THREE[P] * j + i + THREE[P]] += as1[j];
      as[i] -= as1[2 * THREE[Q] - 1];
      as[i + THREE[M]] -= as1[2 * THREE[Q] - 1];
    }
  }
}

/*
template <class R> vector<R> convolve(vector<R> as, vector<R> bs) {
  if (as.empty() || bs.empty()) return {};
  const int len = as.size() + bs.size() - 1;
  int m = 0;
  for (; 2 * THREE[m] < len; ++m) {}
  as.resize(2 * THREE[m], 0);
  bs.resize(2 * THREE[m], 0);
  inplaceConvolve(m, as.data(), bs.data());
  as.resize(len);
  return as;
}
*/
template <class R> vector<R> convolve(vector<R> as, vector<R> bs) {
  if (as.empty() || bs.empty()) return {};
  const int len = as.size() + bs.size() - 1;
  if (false) {}
#define reg(M) else if (len <= 2 * THREE[M]) { as.resize(2 * THREE[M], 0); bs.resize(2 * THREE[M], 0); inplaceConvolve<M>(as.data(), bs.data()); }
  reg(0)
  reg(1)
  reg(2)
  reg(3)
  reg(4)
  reg(5)
  reg(6)
  reg(7)
  reg(8)
  reg(9)
  reg(10)
  reg(11)
  reg(12)
  reg(13)
  reg(14)
#undef reg
  else { assert(false); }
  as.resize(len);
  return as;
}

}  // namespace radix3

template <> void radix3::div3<unsigned long long>(unsigned long long &a) {
  a *= 12297829382473034411ULL;
}
////////////////////////////////////////////////////////////////////////////////

#include <chrono>
#include <iostream>

using std::cerr;
using std::endl;

void unittest_UInt() {
  using namespace radix3;
  using UInt = unsigned long long;

  // div3
  {
    UInt a = 3ULL;
    div3(a);
    assert(a == 1ULL);
  }

  // fft, invFft
  {
    // p = 2, q = 2
    // over R[y] / (1 + y^9 + y^18)
    // root of unity: y^3
    vector<UInt> as(162);
    for (int k = 0; k < 162; ++k) as[k] = k;
    vector<UInt> bs(162, 0);
    for (int i = 0; i < 9; ++i) {
      for (int ii = 0; ii < 9; ++ii) {
        vector<UInt> a(18);
        for (int j = 0; j < 18; ++j) a[j] = as[18 * ii + j];
        for (int j = 0; j < 3 * ((i * ii) % 9); ++j) {
          std::rotate(a.begin(), a.end() - 1, a.end());
          a[9] -= a[0];
          a[0] = -a[0];
        }
        for (int j = 0; j < 18; ++j) bs[18 * (3 * (i % 3) + i / 3) + j] += a[j];
      }
    }
    /*
    cerr << "as = " << endl;
    for (int i = 0; i < 9; ++i) {
      cerr << "  " << i << ":";
      for (int j = 0; j < 18; ++j) cerr << " " << static_cast<long long>(as[18 * i + j]);
      cerr << endl;
    }
    cerr << "bs = " << endl;
    for (int i = 0; i < 9; ++i) {
      cerr << "  " << i << ":";
      for (int j = 0; j < 18; ++j) cerr << " " << static_cast<long long>(bs[18 * i + j]);
      cerr << endl;
    }
    */
    vector<UInt> cs;
    cs = as;
    fft<4>(cs.data());
    /*
    cerr << "fft(as) = " << endl;
    for (int i = 0; i < 9; ++i) {
      cerr << "  " << i << ":";
      for (int j = 0; j < 18; ++j) cerr << " " << static_cast<long long>(cs[18 * i + j]);
      cerr << endl;
    }
    */
    assert(cs == bs);
    cs = bs;
    invFft<4>(cs.data());
    /*
    cerr << "invFft(bs) = " << endl;
    for (int i = 0; i < 9; ++i) {
      cerr << "  " << i << ":";
      for (int j = 0; j < 18; ++j) cerr << " " << static_cast<long long>(cs[18 * i + j]);
      cerr << endl;
    }
    */
    assert(cs == as);
  }
  {
    // p = 3, q = 4
    // over R[y] / (1 + y^81 + y^162)
    // root of unity: y^9
    vector<UInt> as(4374);
    for (int k = 0; k < 4374; ++k) as[k] = 1ULL * k * k * k;
    vector<UInt> bs(4374, 0);
    for (int i = 0; i < 27; ++i) {
      for (int ii = 0; ii < 27; ++ii) {
        vector<UInt> a(162);
        for (int j = 0; j < 162; ++j) a[j] = as[162 * ii + j];
        for (int j = 0; j < 9 * ((i * ii) % 27); ++j) {
          std::rotate(a.begin(), a.end() - 1, a.end());
          a[81] -= a[0];
          a[0] = -a[0];
        }
        for (int j = 0; j < 162; ++j) bs[162 * (9 * (i % 3) + 3 * (i / 3 % 3) + i / 9) + j] += a[j];
      }
    }
    vector<UInt> cs;
    cs = as;
    fft<7>(cs.data());
    assert(cs == bs);
    cs = bs;
    invFft<7>(cs.data());
    assert(cs == as);
  }

  // convolve
  for (int m = 1; m <= 8; ++m) {
    cerr << "unittest_UInt() convolve m = " << m << endl;
    const int asLen = THREE[m] - 2, bsLen = THREE[m] + 1;
    vector<UInt> as(asLen), bs(bsLen);
    for (int i = 0; i < asLen; ++i) as[i] = 1ULL * i * i;
    for (int j = 0; j < bsLen; ++j) bs[j] = 1ULL * j * j * j;
    vector<UInt> cs(asLen + bsLen - 1, 0);
    for (int i = 0; i < asLen; ++i) for (int j = 0; j < bsLen; ++j) cs[i + j] += as[i] * bs[j];
    assert(convolve(as, bs) == cs);
  }
}

// -----------------------------------------------------------------------------

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void solve_UInt(const int N, const unsigned long long expected) {
  static constexpr int NUM_CASES = 10;
  const auto timerBegin = std::chrono::high_resolution_clock::now();

  unsigned long long ans = 0;
  for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
    vector<unsigned long long> as(N), bs(N);
    for (int i = 0; i < N; ++i) {
      as[i] = xrand();
      as[i] |= static_cast<unsigned long long>(xrand()) << 32;
      bs[i] = xrand();
      bs[i] |= static_cast<unsigned long long>(xrand()) << 32;
    }
    const auto cs = radix3::convolve(as, bs);
    assert(static_cast<int>(cs.size()) == 2 * N - 1);
    for (int i = 0; i < 2 * N - 1; ++i) {
      ans ^= cs[i];
    }
  }

  const auto timerEnd = std::chrono::high_resolution_clock::now();
  cerr << "[UInt] " << NUM_CASES << " cases, N = " << N
       << ": expected = " << expected << ", actual = " << ans << endl;
  cerr << std::chrono::duration_cast<std::chrono::milliseconds>(
      timerEnd - timerBegin).count() << " msec" << endl;
  assert(expected == ans);
}
void measurement_UInt() {
  solve_UInt(1, 11299539965873857103ULL);
  solve_UInt(10, 8192769938738557359ULL);
  solve_UInt(100, 16059599503681582065ULL);
  solve_UInt(1000, 17921991051132454588ULL);
  solve_UInt(10000, 5029812135485743581ULL);
  solve_UInt(100000, 8184441232493384094ULL);
  solve_UInt(1000000, 1527747156683225266ULL);
  solve_UInt((1 << 18) + 1, 14150823564279018700ULL);
  solve_UInt(1 << 19, 6867348852005155522ULL);
  solve_UInt((1 << 19) + 1, 5033523924117732051ULL);
  solve_UInt(1 << 20, 17190999267607652588ULL);
  solve_UInt((1 << 20) + 1, 16947359581302113890ULL);
  solve_UInt(1 << 21, 15901775446809640696ULL);
  solve_UInt(177147, 2539055676773925292ULL);
  solve_UInt(177147 + 1, 14309689244472422109ULL);
  solve_UInt(531441, 4601517573642535777ULL);
  solve_UInt(531441 + 1, 693446521193715319ULL);
  solve_UInt(1594323, 2140580117845734008ULL);
  solve_UInt(1594323 + 1, 38539588570175947ULL);
/*
*/
  // @ DAIVRabbit
}

int main() {
  unittest_UInt();
  measurement_UInt();
  return 0;
}
