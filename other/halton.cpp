// Iteration index in [1, BASE^EXPO)
// BASE^(EXPO) (1 + 1 / BASE) must not overflow.
template <int BASE, int EXPO> struct Halton {
  int b, ds[EXPO];
  int xs[EXPO];
  int y;
  Halton() {
    b = 1;
    for (int i = 0; i < EXPO; ++i) b *= BASE;
    ds[EXPO - 1] = 1 + BASE;
    for (int i = EXPO - 1; --i >= 0; ) ds[i] = ds[i + 1] * BASE;
    for (int i = 0; i < EXPO; ++i) ds[i] -= b;
    for (int i = 0; i < EXPO; ++i) xs[i] = 0;
    y = 0;
  }
  double gen() {
    for (int i = 0; i < EXPO; ++i) {
      if (++xs[i] == BASE) {
        xs[i] = 0;
      } else {
        y += ds[i];
        break;
      }
    }
    return y / static_cast<double>(b);
  }
};
using Halton2 = Halton<2, 30>;
using Halton3 = Halton<3, 19>;
using Halton5 = Halton<5, 13>;
using Halton7 = Halton<7, 10>;
using Halton11 = Halton<11, 8>;
using Halton13 = Halton<13, 8>;
using Halton17 = Halton<17, 7>;
using Halton19 = Halton<19, 7>;

////////////////////////////////////////////////////////////////////////////////

#include <assert.h>
#include <stdio.h>

void unittest() {
  {
    Halton2 h;
    printf("2: %d %d\n", h.b, h.ds[0] + h.b);
    assert(h.gen() == 1 / static_cast<double>(2));
    assert(h.gen() == 1 / static_cast<double>(4));
    assert(h.gen() == 3 / static_cast<double>(4));
    assert(h.gen() == 1 / static_cast<double>(8));
    assert(h.gen() == 5 / static_cast<double>(8));
    assert(h.gen() == 3 / static_cast<double>(8));
    assert(h.gen() == 7 / static_cast<double>(8));
    assert(h.gen() ==  1 / static_cast<double>(16));
    assert(h.gen() ==  9 / static_cast<double>(16));
    assert(h.gen() ==  5 / static_cast<double>(16));
    assert(h.gen() == 13 / static_cast<double>(16));
    assert(h.gen() ==  3 / static_cast<double>(16));
    assert(h.gen() == 11 / static_cast<double>(16));
    assert(h.gen() ==  7 / static_cast<double>(16));
    assert(h.gen() == 15 / static_cast<double>(16));
  }
  {
    Halton3 h;
    printf("3: %d %d\n", h.b, h.ds[0] + h.b);
    assert(h.gen() == 1 / static_cast<double>(3));
    assert(h.gen() == 2 / static_cast<double>(3));
    assert(h.gen() == 1 / static_cast<double>(9));
    assert(h.gen() == 4 / static_cast<double>(9));
    assert(h.gen() == 7 / static_cast<double>(9));
    assert(h.gen() == 2 / static_cast<double>(9));
    assert(h.gen() == 5 / static_cast<double>(9));
    assert(h.gen() == 8 / static_cast<double>(9));
    assert(h.gen() ==  1 / static_cast<double>(27));
    assert(h.gen() == 10 / static_cast<double>(27));
    assert(h.gen() == 19 / static_cast<double>(27));
    assert(h.gen() ==  4 / static_cast<double>(27));
    assert(h.gen() == 13 / static_cast<double>(27));
    assert(h.gen() == 22 / static_cast<double>(27));
    assert(h.gen() ==  7 / static_cast<double>(27));
    assert(h.gen() == 16 / static_cast<double>(27));
    assert(h.gen() == 25 / static_cast<double>(27));
    assert(h.gen() ==  2 / static_cast<double>(27));
  }
  {
    Halton5 h;
    printf("5: %d %d\n", h.b, h.ds[0] + h.b);
  }
  {
    Halton7 h;
    printf("7: %d %d\n", h.b, h.ds[0] + h.b);
  }
  {
    Halton11 h;
    printf("11: %d %d\n", h.b, h.ds[0] + h.b);
  }
  {
    Halton13 h;
    printf("13: %d %d\n", h.b, h.ds[0] + h.b);
  }
  {
    Halton17 h;
    printf("17: %d %d\n", h.b, h.ds[0] + h.b);
  }
  {
    Halton19 h;
    printf("19: %d %d\n", h.b, h.ds[0] + h.b);
  }
}

int main() {
  unittest();
  return 0;
}
