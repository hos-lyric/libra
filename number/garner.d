// a^-1 (mod m)
long modInv(long a, long m)
in {
  assert(m > 0, "modInv: m > 0 must hold");
}
do {
  long b = m, x = 1, y = 0, t;
  for (; ; ) {
    t = a / b; a -= t * b;
    if (a == 0) {
      assert(b == 1 || b == -1, "modInv: gcd(a, m) != 1");
      if (b == -1) y = -y;
      return (y < 0) ? (y + m) : y;
    }
    x -= t * y;
    t = b / a; b -= t * a;
    if (b == 0) {
      assert(a == 1 || a == -1, "modInv: gcd(a, m) != 1");
      if (a == -1) x = -x;
      return (x < 0) ? (x + m) : x;
    }
    y -= t * x;
  }
}

// Find the smallest x (>= 0) s.t. x == a[i] (mod m[i]), mod m0
//   m[i]'s must be coprime
//   x = y[0] + m[0] y[1] + m[0] m[1] y[2] + ... + m[0] ... m[n - 1] y[n - 1]
long garner(long[] a, long[] m, long m0)
in {
  foreach (i; 0 .. m.length) {
    assert(0 < m[i] && m[i] <= 0x7fffffff, "garner: 0 < m < 2^31 must hold");
  }
  assert(0 < m0 && m0 <= 0x7fffffff, "garner: 0 < m0 < 2^31 must hold");
}
do {
  long t;
  auto y = new long[m.length];
  foreach (i; 0 .. m.length) {
    y[i] = a[i] % m[i];
    t = 1;
    foreach (j; 0 .. i) {
      (y[i] -= t * y[j]) %= m[i];
      (t *= m[j]) %= m[i];
    }
    if (((y[i] *= modInv(t, m[i])) %= m[i]) < 0) {
      y[i] += m[i];
    }
  }
  long x = 0;
  t = 1;
  foreach (i; 0 .. m.length) {
    (x += t * y[i]) %= m0;
    (t *= m[i]) %= m0;
  }
  return x;
}

unittest {
  long[] a = [314_159_265_358_979_323L, 846_264_338_327_950_288L,
              419_716_939_937_510_582L, 97_494_459_230_781_640L];
  long[] m = [2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23, 1009 * 1013 * 1019,
              10007 * 10009, 10^^9 + 7];
  long m0 = 2_109_876_543;
  assert(garner(a, m, m0) == 227_198_113);
}

void main() {
}
