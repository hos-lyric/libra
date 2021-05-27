import modint;

unittest {
  enum MO = 10^^9 + 7;
  alias Mint = ModInt!MO;

  // this
  assert(Mint(2 * MO + 10).x == 10);
  assert(Mint(-2 * MO + 10).x == 10);
  assert(Mint(Mint(2 * MO + 10)).x == 10);

  // opAssign
  auto a = Mint(10);
  (a = 2 * MO + 11) = 2 * MO + 12;
  assert(a.x == 12);

  // opOpAssign(ModInt)
  a += Mint(MO - 10);
  assert(a.x == 2);
  (a -= Mint(10)) -= Mint(10);
  assert(a.x == MO - 18);
  a = Mint(10^^5);
  a *= Mint(10^^6);
  assert(a.x == 10L^^11 % MO);
  a = 2;
  a /= Mint(3);
  static assert((2 + 2 * MO) % 3 == 0);
  assert(a.x == (2 + 2 * MO) / 3);
  a = 3;
  a ^^= 20;
  assert(a.x == 3L^^20 % MO);
  a = 0;
  a ^^= 0;
  assert(a.x == 1);
  a = 2;
  a ^^= -2;
  static assert((1 + MO) % 4 == 0);
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
  static assert((1 + MO) % 2 == 0);
  assert(a.x == (1 + MO) / 2);

  // inv
  a = 10^^7;
  auto b = a.inv;
  assert(0 <= b.x && b.x < MO);
  assert((cast(long)(a.x) * b.x) % MO == 1);

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
  assert((Mint(MO - 6) + (11L * MO - 2)).x == MO - 8);
  assert((Mint(MO - 6) - (11L * MO - 2)).x == MO - 4);
  assert((Mint(MO - 6) * (11L * MO - 2)).x == 12);
  assert((Mint(MO - 6) / (11L * MO - 2)).x == 3);

  // opBinaryRight
  assert(((11L * MO - 6) + Mint(MO - 2)).x == MO - 8);
  assert(((11L * MO - 6) - Mint(MO - 2)).x == MO - 4);
  assert(((11L * MO - 6) * Mint(MO - 2)).x == 12);
  assert(((11L * MO - 6) / Mint(MO - 2)).x == 3);

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

void main() {
}
