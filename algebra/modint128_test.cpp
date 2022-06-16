#include <assert.h>
#include <vector>
#include "modint128.h"

void unittest() {
  // mul128High
  assert(mul128High(toUInt128("335678912345678912345678912345678912345"),
                    toUInt128("321987654321987654321987654321987654321")) ==
         toUInt128("317631696786256649071842720502547336455"));
  assert(mul128High(toUInt128("314159265358979323846264338327950288419"),
                    toUInt128("71693993751058209749445923078164062862")) ==
         toUInt128("66190125016724109407257290542967984755"));
  assert(mul128High(toUInt128("333333333320938463463374607431768211456"),
                    toUInt128("320282366920938463463374607431768211456")) ==
         toUInt128("313741760807962176639461358329103463250"));

  // setM
  // (10^18 + 3) (10^18 + 9)
  constexpr __int128 MO = toInt128("1000000000000000012000000000000000027");
  using Mint = RMModInt128<0>;
  Mint::setM(MO);
  assert(Mint::M == MO);
  assert(Mint::INV_M == toUInt128("288507432199328843684027604388856715795"));
  assert(Mint::TWO256 == toUInt128("605327380409302573901663786569051452"));

  // reduce
  assert(Mint::reduce(toUInt128("589893640600198667967386140198314492")) ==
         toUInt128("123456789123456789123456789123456789"));

  // mulReduce
  assert(Mint::mulReduce(toUInt128("243694313227967038467634447772221695450"),
                         MO - 2) ==
         toUInt128("716153221317480753235381269846605080"));
  assert(Mint::mulReduce(1, 2) ==
         toUInt128("304305716397224068670403761862050416"));

  // this
  assert(Mint(toInt128("123456789123456789123456789123456789")).y ==
         toUInt128("589893640600198667967386140198314492"));
  assert(Mint(static_cast<unsigned __int128>(1) << 127).get() ==
         toUInt128("141183460469229691687303715884101138"));
  assert(Mint(2 * MO + 10).get() == 10);
  assert(Mint(-2 * MO + 10).get() == 10);
  assert(Mint(Mint(2 * MO + 10)).get() == 10);

  // opAssign
  Mint a = Mint(10);
  (a = 2 * MO + 11) = 2 * MO + 12;
  assert(a.get() == 12);

  // opOpAssign(ModInt)
  a += Mint(MO - 10);
  assert(a.get() == 2);
  (a -= Mint(10)) -= Mint(10);
  assert(a.get() == MO - 18);
  a = Mint(static_cast<__int128>(1) << 70);
  a *= Mint(static_cast<__int128>(1) << 80);
  assert(a.get() == toUInt128("705959863931313665449495097847058940"));
  a = 2;
  a /= Mint(3);
  static_assert((2 + MO) % 3 == 0);
  assert(a.get() == (2 + MO) / 3);
  a = 3;
  a = a.pow(100);
  assert(a.get() == toUInt128("11324851930880981621258786914462237"));
  a = 0;
  a = a.pow(0);
  assert(a.get() == 1);
  a = 2;
  a = a.pow(-2);
  static_assert((1 + MO) % 4 == 0);
  assert(a.get() == (1 + MO) / 4);
  a = 10;
  a += (2 * MO + 20);
  assert(a.get() == 30);
  a = 10;
  a -= (2 * MO + 20);
  assert(a.get() == MO - 10);
  a = 10;
  a *= (2 * MO + 20);
  assert(a.get() == 200);
  a = 10;
  a /= (2 * MO + 20);
  static_assert((1 + MO) % 2 == 0);
  assert(a.get() == (1 + MO) / 2);

  // inv
  a = 10000000;
  Mint b = a.inv();
  assert(b.get() == toUInt128("703703700000000008444444400000000019"));
  assert((a * b).get() == 1);

  // opUnary
  a = 0;
  assert((+a).get() == 0);
  assert((-a).get() == 0);
  a = MO - 1;
  assert((+a).get() == MO - 1);
  assert((-a).get() == 1);

  // opBinary
  assert((Mint(MO - 6) + Mint(MO - 2)).get() == MO - 8);
  assert((Mint(MO - 6) - Mint(MO - 2)).get() == MO - 4);
  assert((Mint(MO - 6) * Mint(MO - 2)).get() == 12);
  assert((Mint(MO - 6) / Mint(MO - 2)).get() == 3);
  assert((Mint(MO - 6) + (11LL * MO - 2)).get() == MO - 8);
  assert((Mint(MO - 6) - (11LL * MO - 2)).get() == MO - 4);
  assert((Mint(MO - 6) * (11LL * MO - 2)).get() == 12);
  assert((Mint(MO - 6) / (11LL * MO - 2)).get() == 3);

  // opBinaryRight
  assert(((11LL * MO - 6) + Mint(MO - 2)).get() == MO - 8);
  assert(((11LL * MO - 6) - Mint(MO - 2)).get() == MO - 4);
  assert(((11LL * MO - 6) * Mint(MO - 2)).get() == 12);
  assert(((11LL * MO - 6) / Mint(MO - 2)).get() == 3);

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
void unittest_inv() {
  using Mint = RMModInt128<1>;
  Mint::setM(1);
  assert(Mint(0).inv().get() == 0);
  assert(Mint(0).inv().y == 0);
  Mint::setM(3);
  assert(Mint(1).inv().get() == 1);
  assert(Mint(2).inv().get() == 2);
  assert(Mint(1).inv().y == 1);
  assert(Mint(2).inv().y == 2);
  Mint::setM(15);
  assert(Mint(1).inv().get() == 1);
  assert(Mint(2).inv().get() == 8);
  assert(Mint(4).inv().get() == 4);
  assert(Mint(7).inv().get() == 13);
  assert(Mint(8).inv().get() == 2);
  assert(Mint(11).inv().get() == 11);
  assert(Mint(13).inv().get() == 7);
  assert(Mint(14).inv().get() == 14);
  Mint::setM(998244353);
  assert(Mint(499122177).inv().get() == 2);
  assert(Mint(998244352).inv().get() == 998244352);
  {
    constexpr unsigned __int128 MO = (static_cast<unsigned __int128>(1) << 127) - 1;
    Mint::setM(MO);
    for (unsigned __int128 x = 1; x < MO; x += MO / 100) {
      const Mint a(x);
      const Mint b = a.inv();
      assert(a.get() == x);
      assert(b.get() < MO);
      assert(a.y < MO);
      assert(b.y < MO);
      assert((a * b).get() == 1);
    }
  }
}

int main() {
  unittest();
  unittest_inv();
  return 0;
}
