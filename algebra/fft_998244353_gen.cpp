#include <assert.h>
#include <stdio.h>
#include <vector>

using std::vector;

#include "modint.h"

constexpr unsigned MO = 998244353U;
using Mint = ModInt<MO>;

constexpr int K = 23;
static_assert(MO == (119 << K | 1));

constexpr Mint G = 3U;

void printVector(const char *name, const char *len, const vector<Mint> &as) {
  printf("constexpr Mint %s[%s] = {", name, len);
  for (size_t i = 0; i < as.size(); ++i) {
    if (i > 0) printf(", ");
    printf("%uU", as[i].x);
  }
  printf("};\n");
}

int main() {
  assert(G.pow((MO - 1) >> 1).x == MO - 1);

  vector<Mint> FFT_ROOTS(K + 1), INV_FFT_ROOTS(K + 1);
  for (int k = 0; k <= K; ++k) {
    FFT_ROOTS[k] = G.pow((MO - 1) >> k);
    INV_FFT_ROOTS[k] = FFT_ROOTS[k].inv();
  }

  // -(2^(-2) + ... + 2^(-(k+1))) + 2^(-(k+2)) = 1/2 + (3/4) 2^(-k)
  vector<Mint> FFT_RATIOS(K - 1), INV_FFT_RATIOS(K - 1);
  for (int k = 0; k <= K - 2; ++k) {
    FFT_RATIOS[k] = -G.pow(3 * ((MO - 1) >> (k + 2)));
    INV_FFT_RATIOS[k] = FFT_RATIOS[k].inv();
  }
  for (int k = 0; k <= K - 2; ++k) {
    Mint prod = 1;
    for (int l = 0; l < k; ++l) {
      prod /= FFT_ROOTS[l + 2];
    }
    prod *= FFT_ROOTS[k + 2];
    assert(prod == FFT_RATIOS[k]);
  }

  printf("constexpr unsigned MO = %uU;\n", MO);
  printf("constexpr unsigned MO2 = 2U * MO;\n");
  printf("constexpr int FFT_MAX = %d;\n", K);
  printf("using Mint = ModInt<MO>;\n");
#define print(as, len) printVector(#as, len, as)
  print(FFT_ROOTS, "FFT_MAX + 1");
  print(INV_FFT_ROOTS, "FFT_MAX + 1");
  print(FFT_RATIOS, "FFT_MAX - 1");
  print(INV_FFT_RATIOS, "FFT_MAX - 1");
#undef print
  return 0;
}
