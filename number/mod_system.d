import std.typecons : Tuple;

// a x + b y = (+/-) gcd(a, b)
//   (a, 0): g = a, x = 1, y = 0
//   (0, b), (b, b), (-b, b) (b != 0): g = b, x = 0, y = 1
//   otherwise: 2 |x| <= |b|, 2 |y| <= |a|
// T: int, long
S gojo(S)(S a, S b, out S x, out S y) {
  if (b != 0) {
    const S g = gojo(b, a % b, y, x);
    y -= (a / b) * x;
    return g;
  } else {
    x = 1;
    y = 0;
    return a;
  }
}

// x == b0  (mod m0),  x == b1  (mod m1)
// S: signed integer
Tuple!(S, "m", S, "b") modSystem(S)(S m0, S b0, S m1, S b1) {
  import std.algorithm.mutation : swap;
  import std.typecons : tuple;
  assert(m0 >= 1, "[modSystem] m0 >= 1 must hold.");
  assert(m1 >= 1, "[modSystem] m1 >= 1 must hold.");
  if ((b0 %= m0) < 0) b0 += m0;
  if ((b1 %= m1) < 0) b1 += m1;
  if (m0 < m1) {
    swap(m0, m1);
    swap(b0, b1);
  }
  // to avoid overflow
  if (m0 % m1 == 0) {
    if (b0 % m1 != b1) return tuple!(S, "m", S, "b")(S(0), S(0));
    return tuple!(S, "m", S, "b")(m0, b0);
  }
  S z0, z1;
  const S g = gojo(m0, m1, z0, z1);
  b1 -= b0;
  if (b1 % g != 0) return tuple!(S, "m", S, "b")(S(0), S(0));
  (b1 /= g) %= m1;
  m1 /= g;
  b0 += m0 * ((z0 * b1) % m1);
  m0 *= m1;
  if (b0 < 0) b0 += m0;
  return tuple!(S, "m", S, "b")(m0, b0);
}
Tuple!(S, "m", S, "b") modSystem(S)(Tuple!(S, "m", S, "b") mb0, Tuple!(S, "m", S, "b") mb1) {
  return modSystem(mb0.m, mb0.b, mb1.m, mb1.b);
}

// x == bs[i]  (mod ms[i])
// S: signed integer
Tuple!(S, "m", S, "b") modSystem(S)(const(S[]) ms, const(S[]) bs) {
  import std.typecons : tuple;
  assert(ms.length == bs.length, "[modSystem] |ms| = |bs| must hold.");
  const len = cast(int)(ms.length);
  auto mb0 = tuple!(S, "m", S, "b")(1, 0);
  foreach (i; 0 .. len) {
    assert(ms[i] >= 1, "[modSystem] ms[i] >= 1 must hold.");
    mb0 = modSystem(mb0.m, mb0.b, ms[i], bs[i]);
    if (!mb0.m) return tuple!(S, "m", S, "b")(0, 0);
  }
  return mb0;
}
Tuple!(S, "m", S, "b") modSystem(S)(const(Tuple!(S, "m", S, "b")[]) mbs) {
  import std.typecons : tuple;
  auto mb0 = tuple!(S, "m", S, "b")(1, 0);
  foreach (mb1; mbs) {
    assert(mb1.m >= 1, "[modSystem] mbs[i].m >= 1 must hold.");
    mb0 = modSystem(mb0, mb1);
    if (!mb0.m) return tuple!(S, "m", S, "b")(0, 0);
  }
  return mb0;
}

// TODO: modSystem(ms, as, bs)

// gojo
unittest {
  import std.math : abs;
  import std.numeric : gcd;
  {
    int x, y;
    assert(gojo(39, 15, x, y) == 3);
    assert(x == 2);
    assert(y == -5);
  }
  // TODO: test large values
  {
    enum long lim = 1000;
    foreach (a; -lim .. lim + 1) foreach (b; -lim .. lim + 1) {
      long x, y;
      const long g = gojo(a, b, x, y);
      // gcd for negative numbers differs between DMD and LDC.
      assert(abs(g) == gcd(abs(a), abs(b)));
      assert(a * x + b * y == g);
      if (b == 0) {
        assert(g == a);
        assert(x == 1);
        assert(y == 0);
      } else if (a == 0 || abs(a) == abs(b)) {
        assert(g == b);
        assert(x == 0);
        assert(y == 1);
      } else {
        assert(2 * abs(x) <= abs(b));
        assert(2 * abs(y) <= abs(a));
      }
    }
  }
}

// modSystem
unittest {
  import std.bigint : BigInt;
  import std.typecons : tuple;
  import std.numeric : gcd;
  assert(modSystem(6, 13, 10, -1) == tuple!(int, "m", int, "b")(30, 19));
  assert(modSystem([tuple!(int, "m", int, "b")(6, 5), tuple!(int, "m", int, "b")(10, 8)]) == tuple!(int, "m", int, "b")(0, 0));
  assert(modSystem(BigInt(10^^9 + 7) * BigInt(10^^9 + 9), BigInt(193000001008L),
                   BigInt(10^^9 + 7) * BigInt(10^^9 + 21), BigInt(637000004116L)) ==
         tuple!(BigInt, "m", BigInt, "b")(BigInt(10^^9 + 7) * BigInt(10^^9 + 9) * BigInt(10^^9 + 21), BigInt(10)^^27));
  assert(modSystem(BigInt(10^^9 + 7) * BigInt(10^^9 + 9), BigInt(193000001008L),
                   BigInt(10^^9 + 7) * BigInt(10^^9 + 21), BigInt(637000004117L)) ==
         tuple!(BigInt, "m", BigInt, "b")(BigInt(0), BigInt(0)));
  // TODO: test large values
  {
    enum long lim = 100;
    foreach (m0; 1 .. lim + 1) foreach (b0; -lim .. lim + 1) {
      const res = modSystem([m0], [b0]);
      assert(res.m == m0);
      assert(0 <= res.b); assert(res.b < m0);
      assert((res.b - b0) % m0 == 0);
    }
  }
  {
    enum long lim = 50;
    foreach (m0; 1 .. lim + 1) foreach (m1; 1 .. lim + 1) {
      const l = m0 / gcd(m0, m1) * m1;
      auto tab = new long[][](m0, m1);
      foreach (b0; 0 .. m0) tab[b0][] = -1;
      foreach (x; 0 .. l) tab[x % m0][x % m1] = x;
      foreach (b0; -lim .. lim + 1) foreach (b1; -lim .. lim + 1) {
        const x = tab[(b0 % m0 + m0) % m0][(b1 % m1 + m1) % m1];
        const res = modSystem([m0, m1], [b0, b1]);
        if (~x) {
          assert(res.m == l);
          assert(res.b == x);
        } else {
          assert(res.m == 0);
          assert(res.b == 0);
        }
      }
    }
  }
  {
    enum long lim = 20;
    foreach (m0; 1 .. lim + 1) foreach (m1; 1 .. lim + 1) foreach (m2; 1 .. lim + 1) {
      long l = m0 / gcd(m0, m1) * m1;
      l = l / gcd(l, m2) * m2;
      auto tab = new long[][][](m0, m1, m2);
      foreach (b0; 0 .. m0) foreach (b1; 0 .. m1) tab[b0][b1][] = -1;
      foreach (x; 0 .. l) tab[x % m0][x % m1][x % m2] = x;
      foreach (b0; 0 .. m0) foreach (b1; 0 .. m1) foreach (b2; 0 .. m2) {
        const x = tab[b0][b1][b2];
        const res = modSystem([m0, m1, m2], [b0, b1, b2]);
        if (~x) {
          assert(res.m == l);
          assert(res.b == x);
        } else {
          assert(res.m == 0);
          assert(res.b == 0);
        }
      }
    }
  }
}

void main() {
}
