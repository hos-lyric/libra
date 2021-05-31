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

template <class R> inline constexpr R INV3();

template <class R> inline void zero(int q, R *as) {
  memset(as, 0, (2 * THREE[q]) * sizeof(R));
}
template <class R> inline void cpy(int q, R *as, R *bs) {
  memcpy(as, bs, (2 * THREE[q]) * sizeof(R));
}
template <class R> inline void add(int q, R *as, R *bs) {
  for (int j = 0; j < 2 * THREE[q]; ++j) as[j] += bs[j];
}
template <class R> inline void add2(int q, R *as, R *bs) {
  for (int j = 0; j < 2 * THREE[q]; ++j) as[j] += 2 * bs[j];
}
template <class R> inline void mulAdd(int q, R *as, R *bs, int r) {
  if (r >= THREE[q + 1]) r -= THREE[q + 1];
  const int j2 = max(2 * THREE[q] - r, 0);
  const int j3 = min(THREE[q + 1] - r, 2 * THREE[q]);
  for (int j = 0; j < j2; ++j) as[j + r] += bs[j];
  for (int j = j2; j < j3; ++j) { as[j + r - 2 * THREE[q]] -= bs[j]; as[j + r - THREE[q]] -= bs[j]; }
  for (int j = j3; j < 2 * THREE[q]; ++j) as[j + r - THREE[q + 1]] += bs[j];
}
template <class R> inline void mulAdd2(int q, R *as, R *bs, int r) {
  if (r >= THREE[q + 1]) r -= THREE[q + 1];
  const int j2 = max(2 * THREE[q] - r, 0);
  const int j3 = min(THREE[q + 1] - r, 2 * THREE[q]);
  for (int j = 0; j < j2; ++j) as[j + r] += 2 * bs[j];
  for (int j = j2; j < j3; ++j) { as[j + r - 2 * THREE[q]] -= 2 * bs[j]; as[j + r - THREE[q]] -= 2 * bs[j]; }
  for (int j = j3; j < 2 * THREE[q]; ++j) as[j + r - THREE[q + 1]] += 2 * bs[j];
}
template <class R> inline void mulSub(int q, R *as, R *bs, int r) {
  if (r >= THREE[q + 1]) r -= THREE[q + 1];
  const int j2 = max(2 * THREE[q] - r, 0);
  const int j3 = min(THREE[q + 1] - r, 2 * THREE[q]);
  for (int j = 0; j < j2; ++j) as[j + r] -= bs[j];
  for (int j = j2; j < j3; ++j) { as[j + r - 2 * THREE[q]] += bs[j]; as[j + r - THREE[q]] += bs[j]; }
  for (int j = j3; j < 2 * THREE[q]; ++j) as[j + r - THREE[q + 1]] -= bs[j];
}
template <class R> inline void mulSub2(int q, R *as, R *bs, int r) {
  if (r >= THREE[q + 1]) r -= THREE[q + 1];
  const int j2 = max(2 * THREE[q] - r, 0);
  const int j3 = min(THREE[q + 1] - r, 2 * THREE[q]);
  for (int j = 0; j < j2; ++j) as[j + r] -= 2 * bs[j];
  for (int j = j2; j < j3; ++j) { as[j + r - 2 * THREE[q]] += 2 * bs[j]; as[j + r - THREE[q]] += 2 * bs[j]; }
  for (int j = j3; j < 2 * THREE[q]; ++j) as[j + r - THREE[q + 1]] -= 2 * bs[j];
}

// DFT of size 3^p over R[y] / (1 + y^(3^q) + y^(2 3^q))
template <class R> void fft(int m, R *as) {
  const int p = m / 2, q = m - m / 2;
  vector<R> ratios(p, 0);
  for (int g = 0; g < p - 1; ++g) ratios[g] = (2 * THREE[q] + 4 * THREE[q - g - 1]) % THREE[q + 1];
  vector<R> work1(2 * THREE[q]), work2(2 * THREE[q]);
  for (int l = p; --l >= 0; ) {
    int prod = 0;
    for (int h = 0, i0 = 0; i0 < THREE[p]; i0 += THREE[l + 1]) {
      for (int i = i0; i < i0 + THREE[l]; ++i) {
        R *a0 = as + 2 * THREE[q] * i;
        R *a1 = as + 2 * THREE[q] * (i + THREE[l]);
        R *a2 = as + 2 * THREE[q] * (i + 2 * THREE[l]);
        zero(q, work1.data());
        mulAdd(q, work1.data(), a1, prod);
        zero(q, work2.data());
        mulAdd(q, work2.data(), a2, 2 * prod);
        cpy(q, a1, a0);
        mulAdd(q, a1, work1.data(), THREE[q]);
        mulAdd(q, a1, work2.data(), 2 * THREE[q]);
        cpy(q, a2, a0);
        mulAdd(q, a2, work1.data(), 2 * THREE[q]);
        mulAdd(q, a2, work2.data(), THREE[q]);
        add(q, a0, work1.data());
        add(q, a0, work2.data());
      }
      int g = 0;
      for (int hh = ++h; hh % 3 == 0; hh /= 3) ++g;
      if ((prod += ratios[g]) >= THREE[q + 1]) prod -= THREE[q + 1];
    }
  }
}

// inverse DFT of size 3^p over R[y] / (1 + y^(3^q) + y^(2 3^q))
template <class R> void invFft(int m, R *as) {
  const int p = m / 2, q = m - m / 2;
  vector<R> invRatios(p, 0);
  for (int g = 0; g < p - 1; ++g) invRatios[g] = (4 * THREE[q] - 4 * THREE[q - g - 1]) % THREE[q + 1];
  vector<R> work1(2 * THREE[q]), work2(2 * THREE[q]);
  for (int l = 0; l < p; ++l) {
    int prod = 0;
    for (int h = 0, i0 = 0; i0 < THREE[p]; i0 += THREE[l + 1]) {
      for (int i = i0; i < i0 + THREE[l]; ++i) {
        R *a0 = as + 2 * THREE[q] * i;
        R *a1 = as + 2 * THREE[q] * (i + THREE[l]);
        R *a2 = as + 2 * THREE[q] * (i + 2 * THREE[l]);
        cpy(q, work1.data(), a0);
        mulAdd(q, work1.data(), a1, 2 * THREE[q]);
        mulAdd(q, work1.data(), a2, THREE[q]);
        cpy(q, work2.data(), a0);
        mulAdd(q, work2.data(), a1, THREE[q]);
        mulAdd(q, work2.data(), a2, 2 * THREE[q]);
        add(q, a0, a1);
        add(q, a0, a2);
        zero(q, a1);
        mulAdd(q, a1, work1.data(), prod);
        zero(q, a2);
        mulAdd(q, a2, work2.data(), 2 * prod);
      }
      int g = 0;
      for (int hh = ++h; hh % 3 == 0; hh /= 3) ++g;
      if ((prod += invRatios[g]) >= THREE[q + 1]) prod -= THREE[q + 1];
    }
  }
  R inv3 = 1;
  for (int l = 0; l < p; ++l) inv3 *= INV3<R>();
  for (int k = 0; k < 2 * THREE[m]; ++k) as[k] *= inv3;
}

// a <- a b mod (1 + x^(3^m) + x^(2 3^m))
template <class R> void inplaceConvolve(int m, R *as, R *bs) {
  if (m <= 3) {
    vector<R> cs(4 * THREE[m] - 1, 0);
    for (int ka = 0; ka < 2 * THREE[m]; ++ka) for (int kb = 0; kb < 2 * THREE[m]; ++kb) cs[ka + kb] += as[ka] * bs[kb];
    for (int k = 4 * THREE[m] - 1; --k >= 2 * THREE[m]; ) {
      cs[k - 2 * THREE[m]] -= cs[k];
      cs[k - THREE[m]] -= cs[k];
    }
    memcpy(as, cs.data(), (2 * THREE[m]) * sizeof(R));
  } else {
    // y := x^(3^p)
    // (R[y] / (1 + y^(3^q) + y^(2 3^q)))[x]
    const int p = m / 2, q = m - m / 2;
    vector<R> as0(2 * THREE[m]), bs0(2 * THREE[m]), as1(2 * THREE[m], 0), bs1(2 * THREE[m], 0);
    for (int j = 0; j < 2 * THREE[q]; ++j) for (int i = 0; i < THREE[p]; ++i) as0[2 * THREE[q] * i + j] = as[THREE[p] * j + i];
    for (int j = 0; j < 2 * THREE[q]; ++j) for (int i = 0; i < THREE[p]; ++i) bs0[2 * THREE[q] * i + j] = bs[THREE[p] * j + i];
    // x <- y^(3^q/3^p) x
    for (int i = 0; i < THREE[p]; ++i) mulAdd(q, as1.data() + 2 * THREE[q] * i, as0.data() + 2 * THREE[q] * i, THREE[q - p] * i);
    for (int i = 0; i < THREE[p]; ++i) mulAdd(q, bs1.data() + 2 * THREE[q] * i, bs0.data() + 2 * THREE[q] * i, THREE[q - p] * i);
    fft(m, as0.data());
    fft(m, bs0.data());
    for (int i = 0; i < THREE[p]; ++i) inplaceConvolve(q, bs0.data() + 2 * THREE[q] * i, as0.data() + 2 * THREE[q] * i);
    invFft(m, bs0.data());
    fft(m, as1.data());
    fft(m, bs1.data());
    for (int i = 0; i < THREE[p]; ++i) inplaceConvolve(q, bs1.data() + 2 * THREE[q] * i, as1.data() + 2 * THREE[q] * i);
    invFft(m, bs1.data());
    zero(m, as);
    for (int i = 0; i < THREE[p]; ++i) {
      // b0 = c0 + c1
      // b1 = y^(3^q/3^p i) c0 + y^(3^q/3^p i + 3^q) c1
      // c0 = (1/3) (2 + y^(3^q)) (-y^(3^q) b0 + y^(-3^q/3^p i) b1)
      // c1 = (1/3) (2 + y^(3^q)) (b0 - y^(-3^q/3^p i) b1)
      R *b0 = bs0.data() + 2 * THREE[q] * i;
      R *b1 = bs1.data() + 2 * THREE[q] * i;
      for (int j = 0; j < 2 * THREE[q]; ++j) b0[j] *= INV3<R>();
      for (int j = 0; j < 2 * THREE[q]; ++j) b1[j] *= INV3<R>();
      zero(q, as0.data());
      mulSub2(q, as0.data(), b0, THREE[q]);
      mulSub(q, as0.data(), b0, 2 * THREE[q]);
      mulAdd2(q, as0.data(), b1, THREE[q + 1] - THREE[q - p] * i);
      mulAdd(q, as0.data(), b1, THREE[q + 1] - THREE[q - p] * i + THREE[q]);
      zero(q, as1.data());
      add2(q, as1.data(), b0);
      mulAdd(q, as1.data(), b0, THREE[q]);
      mulSub2(q, as1.data(), b1, THREE[q + 1] - THREE[q - p] * i);
      mulSub(q, as1.data(), b1, THREE[q + 1] - THREE[q - p] * i + THREE[q]);
      for (int j = 0; j < 2 * THREE[q]; ++j) as[THREE[p] * j + i] += as0[j];
      for (int j = 0; j < 2 * THREE[q] - 1; ++j) as[THREE[p] * j + i + THREE[p]] += as1[j];
      as[i] -= as1[2 * THREE[q] - 1];
      as[i + THREE[m]] -= as1[2 * THREE[q] - 1];
    }
  }
}

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

}  // namespace radix3

template <> constexpr unsigned long long radix3::INV3<unsigned long long>() {
  return 12297829382473034411ULL;
}
////////////////////////////////////////////////////////////////////////////////

#include <chrono>
#include <iostream>

using std::cerr;
using std::endl;

void unittest_UInt() {
  using namespace radix3;
  using UInt = unsigned long long;

  // INV3
  assert(3ULL * INV3<UInt>() == 1ULL);

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
    fft(4, cs.data());
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
    invFft(4, cs.data());
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
    fft(7, cs.data());
    assert(cs == bs);
    cs = bs;
    invFft(7, cs.data());
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
