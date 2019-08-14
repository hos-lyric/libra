// a^-1 (mod 2^64)
long modInv(long a)
in {
  assert(a & 1, "modInv: a must be odd");
}
do {
  long b = ((a << 1) + a) ^ 2;
  b *= 2 - a * b;
  b *= 2 - a * b;
  b *= 2 - a * b;
  b *= 2 - a * b;
  return b;
}

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

// modInv
unittest {
  for (long a = -99; a <= 99; a += 2) {
    assert(a * modInv(a) == 1);
  }
  assert(123456789123456789L * modInv(123456789123456789L) == 1);
  foreach (m; 1 .. 10) {
    foreach (a; -9 .. 100) {
      bool coprime = true;
      foreach (g; 2 .. 100) {
        if (m % g == 0 && a % g == 0) {
          coprime = false;
        }
      }
      if (coprime) {
        const b = modInv(a, m);
        assert(0 <= b && b < m);
        assert((a * b - 1) % m == 0);
      }
    }
  }
}

void main() {
}
