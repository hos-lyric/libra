#include <assert.h>
#include "modint.h"

void unittest() {
  constexpr int MO = 1000000007;
  using Mint = ModInt<MO>;

  // this
  assert(Mint(2 * MO + 10).x == 10);
  assert(Mint(-2 * MO + 10).x == 10);
  assert(Mint(Mint(2 * MO + 10)).x == 10);

  // opAssign
  Mint a = Mint(10);
  (a = 2 * MO + 11) = 2 * MO + 12;
  assert(a.x == 12);

  // opOpAssign(ModInt)
  a += Mint(MO - 10);
  assert(a.x == 2);
  (a -= Mint(10)) -= Mint(10);
  assert(a.x == MO - 18);
  a = Mint(100000);
  a *= Mint(1000000);
  assert(a.x == 100000000000LL % MO);
  a = 2;
  a /= Mint(3);
  static_assert((2 + 2 * MO) % 3 == 0);
  assert(a.x == (2 + 2 * MO) / 3);
  a = 3;
  a = a.pow(20);
  assert(a.x == 3486784401LL % MO);
  a = 0;
  a = a.pow(0);
  assert(a.x == 1);
  a = 2;
  a = a.pow(-2);
  static_assert((1 + MO) % 4 == 0);
  assert(a.x == (1 + MO) / 4);
  a = 10;
  a += (2 * MO + 20);
  assert(a.x == 30);
  a = 10;
  a -= (2 * MO + 20);
  assert(a.x == MO - 10);
  a = 10;
  a *= (2 * MO + 20);
  assert(a.x == 200);
  a = 10;
  a /= (2 * MO + 20);
  static_assert((1 + MO) % 2 == 0);
  assert(a.x == (1 + MO) / 2);

  // inv
  a = 10000000;
  Mint b = a.inv();
  assert(b.x < MO);
  assert((static_cast<long>(a.x) * b.x) % MO == 1);

  // opUnary
  a = 0;
  assert((+a).x == 0);
  assert((-a).x == 0);
  a = MO - 1;
  assert((+a).x == MO - 1);
  assert((-a).x == 1);

  // opBinary
  assert((Mint(MO - 6) + Mint(MO - 2)).x == MO - 8);
  assert((Mint(MO - 6) - Mint(MO - 2)).x == MO - 4);
  assert((Mint(MO - 6) * Mint(MO - 2)).x == 12);
  assert((Mint(MO - 6) / Mint(MO - 2)).x == 3);
  assert((Mint(MO - 6) + (11LL * MO - 2)).x == MO - 8);
  assert((Mint(MO - 6) - (11LL * MO - 2)).x == MO - 4);
  assert((Mint(MO - 6) * (11LL * MO - 2)).x == 12);
  assert((Mint(MO - 6) / (11LL * MO - 2)).x == 3);

  // opBinaryRight
  assert(((11LL * MO - 6) + Mint(MO - 2)).x == MO - 8);
  assert(((11LL * MO - 6) - Mint(MO - 2)).x == MO - 4);
  assert(((11LL * MO - 6) * Mint(MO - 2)).x == 12);
  assert(((11LL * MO - 6) / Mint(MO - 2)).x == 3);

  // opCast
  a = MO;
  assert(!a);
  a = MO + 1;
  assert(a);

  // opEquals
  a = 2;
  b = MO + 2;
  assert(a == b);
  b = MO - 2;
  assert(a != b);
}

// ModInt::inv
void unittestInv() {
  assert(ModInt<1>(0).inv().x == 0);
  assert(ModInt<2>(1).inv().x == 1);
  assert(ModInt<3>(1).inv().x == 1);
  assert(ModInt<3>(2).inv().x == 2);
  assert(ModInt<4>(1).inv().x == 1);
  assert(ModInt<4>(3).inv().x == 3);
  assert(ModInt<10>(1).inv().x == 1);
  assert(ModInt<10>(3).inv().x == 7);
  assert(ModInt<10>(7).inv().x == 3);
  assert(ModInt<10>(9).inv().x == 9);
  assert(ModInt<998244353>(499122177).inv().x == 2);
  assert(ModInt<998244353>(998244352).inv().x == 998244352);
}

int main() {
  unittest();
  unittestInv();
  return 0;
}
