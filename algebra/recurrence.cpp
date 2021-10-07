#include <assert.h>
#include <stdio.h>
#include <vector>

#include "modint.h"

using std::vector;

// 0 = \sum_{j=0}^d (\sum_{k=0}^e css[j][k] i^k) as[i - j]  (d <= i < |as|)
template <unsigned M>
vector<vector<ModInt<M>>> findPRecurrence(const vector<ModInt<M>> &as, int e,
                                          bool verbose = false) {
  using Mint = ModInt<M>;
  const int asLen = as.size();
  // asLen - d >= (d + 1) (e + 1) - 1  (otherwise definitely  dim Ker >= 2)
  const int d0 = (asLen + 2) / (e + 2) - 1;
  if (d0 < 0) {
    if (verbose) {
      fprintf(stderr, "[findPRecurrence] |as| >= e  must hold.\n");
      fflush(stderr);
    }
    return {};
  }
  const int m = asLen - d0, n = (d0 + 1) * (e + 1);
  vector<vector<Mint>> bss(m, vector<Mint>(n, 0));
  for (int i = d0; i < asLen; ++i) for (int j = 0; j <= d0; ++j) {
    Mint pw = 1;
    for (int k = 0; k <= e; ++k) {
      bss[i - d0][j * (e + 1) + k] = pw * as[i - j];
      pw *= i;
    }
  }
// for(int i=0;i<m;++i){printf("bss[%d] =",i);for(int j=0;j<n;++j){printf(" %u",bss[i][j].x);}puts("");}
  int r = 0;
  vector<int> hs;
  for (int h = 0; h < n; ++h) {
    for (int i = r; i < m; ++i) if (bss[i][h]) {
      bss[r].swap(bss[i]);
      break;
    }
    if (r < m && bss[r][h]) {
      const Mint s = bss[r][h].inv();
      for (int j = h; j < n; ++j) bss[r][j] *= s;
      for (int i = 0; i < m; ++i) if (i != r) {
        const Mint t = bss[i][h];
        for (int j = h; j < n; ++j) bss[i][j] -= t * bss[r][j];
      }
      ++r;
    } else {
      hs.push_back(h);
    }
  }
// for(int i=0;i<m;++i){printf("bss[%d] =",i);for(int j=0;j<n;++j){printf(" %u",bss[i][j].x);}puts("");}
  if (hs.empty()) {
    if (verbose) {
      fprintf(stderr, "[findPRecurrence] Not found: d = %d, e = %d.\n", d0, e);
      fflush(stderr);
    }
    return {};
  }
  vector<vector<Mint>> css(d0 + 1, vector<Mint>(e + 1, 0));
  for (int j = 0; j <= d0; ++j) for (int k = 0; k <= e; ++k) {
    const int h = j * (e + 1) + k;
    css[j][k] = (h < hs[0]) ? -bss[h][hs[0]] : (h == hs[0]) ? 1 : 0;
  }
  int d = hs[0] / (e + 1);
  for (int i = d0; i < asLen; ++i) {
    Mint sum = 0;
    for (int j = 0; j <= d0; ++j) {
      Mint coef = 0, pw = 1;
      for (int k = 0; k <= e; ++k) {
        coef += css[j][k] * pw;
        pw *= i;
      }
      sum += coef * as[i - j];
    }
    for (; sum; ) {
      if (i - ++d < 0) break;
      assert(d <= d0);
      Mint coef = 0, pw = 1;
      for (int k = 0; k <= e; ++k) {
        coef += css[d][k] * pw;
        pw *= i;
      }
      sum += coef * as[i - d];
    }
  }
  css.resize(d + 1);
  if (verbose) {
    const int hsLen = hs.size();
    if (hsLen > d0 - d + 1) {
      fprintf(stderr, "[findPRecurrence] Degenerate? (dim Ker = %d)\n", hsLen);
    }
    fprintf(stderr, "[findPRecurrence] d = %d, e = %d, non-trivial: %d\n", d, e,
            asLen - d - (d + 1) * (e + 1) + 1);
    fprintf(stderr, "{\n");
    for (int j = 0; j <= d; ++j) {
      fprintf(stderr, "  {");
      for (int k = 0; k <= e; ++k) {
        const unsigned c = css[j][k].x;
        if (k > 0) fprintf(stderr, ", ");
        fprintf(stderr, "%d", static_cast<int>((c < M - c) ? c : (c - M)));
      }
      fprintf(stderr, "},\n");
    }
    fprintf(stderr, "}\n");
    fflush(stderr);
  }
  return css;
}

// 0 = \sum_{j=0}^d (\sum_{k=0}^e css[j][k] i^k) as[i - j]  (d <= i < |as|)
template <unsigned M>
vector<ModInt<M>> extendPRecurrence(vector<ModInt<M>> as,
                                    const vector<vector<ModInt<M>>> &css,
                                    int n) {
  using Mint = ModInt<M>;
  assert(!css.empty());
  const int d = css.size() - 1, e = css[0].size() - 1;
  for (int j = 0; j <= d; ++j) assert(static_cast<int>(css[j].size()) == e + 1);
  const int asLen = as.size();
  as.resize(n);
  for (int i = asLen; i < n; ++i) {
    Mint sum = 0;
    for (int j = 1; j <= d; ++j) {
      Mint coef = 0, pw = 1;
      for (int k = 0; k <= e; ++k) {
        coef += css[j][k] * pw;
        pw *= i;
      }
      sum += coef * as[i - j];
    }
    {
      Mint coef = 0, pw = 1;
      for (int k = 0; k <= e; ++k) {
        coef += css[0][k] * pw;
        pw *= i;
      }
      as[i] = -sum / coef;
    }
  }
  return as;
}

////////////////////////////////////////////////////////////////////////////////

void unittest() {
  constexpr unsigned MO = 998244353;
  using Mint = ModInt<MO>;

  auto test = [&](vector<Mint> as, int asLen, int e,
                  const vector<vector<Mint>> &expected) -> void {
    assert(static_cast<int>(as.size()) >= asLen);
    as.resize(asLen);
    fprintf(stderr, "[test] as = [");
    for (int i = 0; i < asLen; ++i) {
      if (i > 0) fprintf(stderr, ", ");
      fprintf(stderr, "%u", as[i].x);
    }
    fprintf(stderr, "], e = %d\n", e);
    fflush(stderr);
    const vector<vector<Mint>> css = findPRecurrence(as, e, true);
    if (!css.empty()) {
      const int d = css.size() - 1, e = css[0].size() - 1;
      for (int j = 0; j <= d; ++j) {
        assert(static_cast<int>(css[j].size()) == e + 1);
      }
      for (int i = d; i < asLen; ++i) {
        Mint sum = 0;
        for (int j = 0; j <= d; ++j) {
          Mint coef = 0, pw = 1;
          for (int k = 0; k <= e; ++k) {
            coef += css[j][k] * pw;
            pw *= i;
          }
          sum += coef * as[i - j];
        }
        assert(!sum);
      }
    }
    assert(css == expected);
  };

  // a[i] = 0
  {
    const vector<Mint> as(10, 0);
    test(as, as.size(), 0, {{1}});
    test(as, as.size(), 1, {{1, 0}});
  }

  // a[i] = 1
  {
    const vector<Mint> as(10, 1);
    test(as, as.size(), 0, {{-1}, {1}});
    test(as, as.size(), 1, {{-1, 0}, {1, 0}});
  }

  // a[i] = i
  {
    vector<Mint> as(10);
    for (int i = 0; i < 10; ++i) as[i] = i;
    test(as, as.size(), 0, {{1}, {-2}, {1}});
    test(as, as.size(), 1, {{1, -1}, {0, 1}});
    test(as, as.size(), 2, {{1, -1, 0}, {0, 1, 0}});
  }

  // a[i] = 1/(i+1)
  {
    vector<Mint> as(10);
    for (int i = 0; i < 10; ++i) as[i] = Mint(i + 1).inv();
    test(as, as.size(), 1, {{-1, -1}, {0, 1}});
    test(as, as.size(), 2, {{-1, -1, 0}, {0, 1, 0}});
  }

  // a[i] = i!
  {
    const vector<Mint> as{1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880};
    test(as, 3, 1, {});
    test(as, 4, 1, {{-1, 0}, {0, 1}});
    test(as, 7, 1, {{-1, 0}, {0, 1}});
    test(as, 10, 2, {{-1, 0, 0}, {0, 1, 0}});
  }

  // a[i] = 1/i!
  {
    vector<Mint> as{1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880};
    for (int i = 0; i < 10; ++i) as[i] = as[i].inv();
    test(as, as.size(), 1, {{0, -1}, {1, 0}});
    test(as, as.size(), 2, {{0, -1, 0}, {1, 0, 0}});
  }

  // a[i] = !i
  // https://oeis.org/A000166
  {
    const vector<Mint> as{1, 0, 1, 2, 9, 44, 265, 1854, 14833, 133496, 1334961,
                          14684570, 176214841, 2290792932LL, 32071101049LL};
    test(as, 7, 1, {{-1, 0}, {-1, 1}, {-1, 1}});
    test(as, as.size(), 1, {{-1, 0}, {-1, 1}, {-1, 1}});
    test(as, as.size(), 2, {{-1, 0, 0}, {-1, 1, 0}, {-1, 1, 0}});
  }

  // a[i] = [x^i y^i] (1 / (1 - x - y - x y))
  // https://oeis.org/A001850
  {
    const vector<Mint> as{1, 3, 13, 63, 321, 1683, 8989, 48639, 265729, 1462563,
                          8097453, 45046719, 251595969, 1409933619,
                          7923848253LL};
    test(as, as.size(), 1, {{0, 1}, {3, -6}, {-1, 1}});
    test(as, as.size(), 2, {{0, 1, 0}, {3, -6, 0}, {-1, 1, 0}});
  }

  // a[i] = [x^i] \sum_{j>=0} j! ((x - x^2) / (1 + x))^j
  // https://oeis.org/A002464
  {
    const vector<Mint> as{1, 1, 0, 0, 2, 14, 90, 646, 5242, 47622, 479306,
                          5296790, 63779034, 831283558, 11661506218LL,
                          175203184374LL};
    test(as, as.size(), 1, {{-1, 0}, {1, 1}, {2, -1}, {5, -1}, {-3, 1}});
    assert(extendPRecurrence(
        vector<Mint>(as.begin(), as.begin() + 14),
        findPRecurrence(vector<Mint>(as.begin(), as.begin() + 13), 1),
        as.size()) == as);
  }

  // a[i] = i! + 1/i!
  {
    vector<Mint> as(100);
    for (int i = 0; i < 100; ++i) {
      as[i] = 1;
      for (int j = 1; j <= i; ++j) as[i] *= j;
      as[i] = as[i] + as[i].inv();
    }
    test(as, as.size(), 2, {
      {0, -1, 0},
      {-1, 1, 1},
      {-6, 3, -1},
      {-11, 7, -1},
      {-3, 1, 0},
    });
    assert(extendPRecurrence(
        vector<Mint>(as.begin(), as.begin() + 50),
        findPRecurrence(vector<Mint>(as.begin(), as.begin() + 50), 2),
        as.size()) == as);
  }
}

int main() {
  unittest();
  return 0;
}
