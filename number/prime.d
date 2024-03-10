// TODO: update like prime.cpp

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

// Factorize n using Pollard's rho algorithm
ulong[] factorize(ulong n)
in {
  assert(n < 1UL << 63, "factorize: n < 2^63 must hold");
}
do {
  import std.algorithm.sorting : merge;
  import std.array : array;
  import std.math : abs;
  import std.numeric : gcd;
  if (n <= 1) return [];
  if (isPrime(n)) return [n];
  if (n % 2 == 0) return [2UL] ~ factorize(n / 2);
  for (ulong c = 1; ; ++c) {
    long x = 2, y = 2, d;
    do {
      x = multiply(x, x, n) + c;
      if (x >= n) x -= n;
      y = multiply(y, y, n) + c;
      if (y >= n) y -= n;
      y = multiply(y, y, n) + c;
      if (y >= n) y -= n;
      d = gcd(abs(x - y), n);
    } while (d == 1);
    if (d < n) {
      return merge(factorize(d), factorize(n / d)).array;
    }
  }
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

// factorize
unittest {
  assert(factorize(1) == []);
  assert(factorize(2) == [2]);
  assert(factorize(3) == [3]);
  assert(factorize(4) == [2, 2]);
  assert(factorize(5) == [5]);
  assert(factorize(6) == [2, 3]);
  assert(factorize(7) == [7]);
  assert(factorize(8) == [2, 2, 2]);
  assert(factorize(9) == [3, 3]);
  assert(factorize(2^^4 * 3^^3 * 5^^2 * 7) == [2, 2, 2, 2, 3, 3, 3, 5, 5, 7]);
  assert(factorize(4294967297UL) == [641, 6700417]);
  assert(factorize(1_000_000_016_000_000_063UL) ==
         [1_000_000_007, 1_000_000_009]);
  assert(factorize(3141592653589793238UL) ==
         [2, 3, 11, 10513, 311743, 14523877]);
  assert(factorize(997748200186314745UL) ==
         [5, 7, 17, 17, 17581, 5610628223UL]);
}

void main() {
}
