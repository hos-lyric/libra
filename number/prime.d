// a b (mod m)
ulong multiply(ulong a, ulong b, ulong m)
in {
  assert(m < 1UL << 63, "multiply: m < 2^63 must hold");
  assert(a < m, "multiply: a < m must hold");
  assert(b < m, "multiply: b < m must hold");
}
do {
  ulong c = 0;
  for (; a; a >>= 1) {
    if (a & 1) {
      c += b;
      if (c >= m) c -= m;
    }
    b <<= 1;
    if (b >= m) b -= m;
  }
  return c;
}

// a^e (mod m)
ulong power(ulong a, ulong e, ulong m)
in {
  assert(m < 1UL << 63, "power: m < 2^63 must hold");
  assert(a < m, "power: a < m must hold");
}
do {
  long b = 1;
  for (; e; e >>= 1) {
    if (e & 1) b = multiply(b, a, m);
    a = multiply(a, a, m);
  }
  return b;
}

// Checks if n is a prime using Miller-Rabin test
bool isPrime(ulong n)
in {
  assert(n < 1UL << 63, "isPrime: n < 2^63 must hold");
}
do {
  import core.bitop : bsf;
  // http://miller-rabin.appspot.com/
  enum ulong[] BASES = [2, 325, 9375, 28178, 450775, 9780504, 1795265022];
  if (n <= 1 || !(n & 1)) return (n == 2);
  const s = bsf(n - 1);
  const d = (n - 1) >> s;
  foreach (base; BASES) {
    ulong a = base % n;
    if (a == 0) continue;
    a = power(a, d, n);
    if (a == 1 || a == n - 1) continue;
    bool ok = false;
    foreach (_; 0 .. s - 1) {
      a = multiply(a, a, n);
      if (a == n - 1) {
        ok = true;
        break;
      }
    }
    if (!ok) return false;
  }
  return true;
}

// multiply
unittest {
  enum a = 9123456789123456789UL;
  enum b = 3141592653589793238UL;
  enum m = 9223372036854775783UL;
  assert(multiply(a, b, m) == 7899513326948043768UL);
  assert(multiply(b, a, m) == 7899513326948043768UL);
}

// power
unittest {
  enum a = 9123456789123456789UL;
  enum e = 3141592653589793238UL;
  enum m = 9223372036854775783UL;
  assert(power(a, e, m) == 6189356224408591002UL);
}

// isPrime
unittest {
  assert(!isPrime(0));
  assert(!isPrime(1));
  foreach (ulong n; 2 .. 10^^5) {
    bool found;
    for (ulong d = 2; d * d <= n; ++d) {
      found = found || (n % d == 0);
    }
    assert(isPrime(n) == !found);
  }
  assert(isPrime(9223372036854775783UL));
  assert(!isPrime(7156857700403137441UL));
}

void main() {
}
