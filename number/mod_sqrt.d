// xorshift
uint xrand() {
  static uint x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  uint t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

// Jacobi symbol (a/m)
int jacobi(long a, long m)
in {
  assert(m > 0, "jacobi: m > 0 must hold");
  assert(m & 1, "jacobi: m must be odd");
}
do {
  import core.bitop : bsf;
  import std.algorithm.mutation : swap;
  int s = 1;
  if (a < 0) a = a % m + m;
  for (; m > 1; ) {
    a %= m;
    if (a == 0) return 0;
    const r = bsf(a);
    if ((r & 1) && ((m + 2) & 4)) s = -s;
    a >>= r;
    if (a & m & 2) s = -s;
    swap(a, m);
  }
  return s;
}

// sqrt(a) (mod p)
//   p: be prime
//   (b + sqrt(b^2 - a))^((p+1)/2) in F_p(sqrt(b^2 - a))
long[] modSqrt(long a, long p)
in {
  assert(p < 1L << 32, "modSqrt: p < 2^32 must hold");
  assert(-p * p <= a && a <= p * p, "modSqrt: -p^2 <= a <= p^2 must hold");
}
do {
  if (p == 2) return [a & 1];
  const j = jacobi(a, p);
  if (j == 0) return [0];
  if (j == -1) return [];
  long b, d;
  for (; ; ) {
    b = xrand() % p;
    d = (b * b - a) % p;
    if (d < 0) d += p;
    if (jacobi(d, p) == -1) break;
  }
  long[2] multiply(in long[2] x, in long[2] y) {
    return [(x[0] * y[0] + d * ((x[1] * y[1]) % p)) % p,
            (x[0] * y[1] + x[1] * y[0]) % p];
  }
  long[2] f = [b, 1], g = [1, 0];
  for (long e = (p + 1) >> 1; e; e >>= 1) {
    if (e & 1) g = multiply(g, f);
    f = multiply(f, f);
  }
  assert(g[1] == 0);
  return (g[0] < p - g[0]) ? [g[0], p - g[0]] : [p - g[0], g[0]];
}

// jacobi
unittest {
  foreach (p; [3, 5, 7, 11, 13, 17, 19, 23, 29]) {
    foreach (a; -2 * p .. 2 * p) {
      int s = -1;
      foreach (x; 0 .. p) {
        if ((x * x - a) % p == 0) {
          ++s;
        }
      }
      assert(s == jacobi(a, p));
    }
  }
  foreach (a; 10L^^18 .. 10L^^18 + 100) {
    assert(jacobi(a, 31) * jacobi(a, 37)^^2 * jacobi(a, 41)^^3 ==
           jacobi(a, 31L * 37L^^2 * 41L^^3));
  }
}

// modSqrt
unittest {
  foreach (p; [3, 5, 7, 11, 13, 17, 19, 23, 29]) {
    int numRoots;
    foreach (a; 0 .. p) {
      foreach (x; modSqrt(a, p)) {
        assert(0 <= x && x < p);
        assert((x * x) % p == a);
        ++numRoots;
      }
      assert(modSqrt(a, p) == modSqrt(a - p, p));
      assert(modSqrt(a, p) == modSqrt(a + p, p));
    }
    assert(numRoots == p);
  }
  assert(modSqrt(123_456_789, 10^^9 + 7) == [151347102, 848652905]);
  assert(modSqrt(123_456_798, 10^^9 + 7) == []);
  assert(modSqrt((2L^^31 - 1)^^2 - 3, 2L^^31 - 1) == [879471824, 1268011823]);
}

void main() {
}
