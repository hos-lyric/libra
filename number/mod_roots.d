// xorshift
uint xrand() {
  static uint x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  uint t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
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

// (a / 2) mod m
long div2(long a, long m)
in {
  assert(1 <= m && m < 1L << 62, "div2: 1 <= m < 2^62 must hold");
  assert(m % 2 != 0, "div2: m must not be divisible by 2");
  assert(0 <= a && a < m, "div2: 0 <= a < m must hold");
}
do {
  return (a + (a % 2) * m) / 2;
}

// (a / 3) mod m
long div3(long a, long m)
in {
  assert(1 <= m && m < 1L << 61, "div3: 1 <= m < 2^61 must hold");
  assert(m % 3 != 0, "div3: m must not be divisible by 3");
  assert(0 <= a && a < m, "div3: 0 <= a < m must hold");
}
do {
  return (a + (((3 - a % 3) * (m % 3)) % 3) * m) / 3;
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
  assert(p < 1L << 31, "modSqrt: p < 2^31 must hold");
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
  long[2] mul(in long[2] x, in long[2] y) {
    return [(x[0] * y[0] + d * ((x[1] * y[1]) % p)) % p,
            (x[0] * y[1] + x[1] * y[0]) % p];
  }
  long[2] f = [b, 1], g = [1, 0];
  for (long e = (p + 1) >> 1; e; e >>= 1) {
    if (e & 1) g = mul(g, f);
    f = mul(f, f);
  }
  assert(g[1] == 0);
  return (g[0] < p - g[0]) ? [g[0], p - g[0]] : [p - g[0], g[0]];
}

// Roots of f0 + f1 T + T^2 in F_p[T] with multiplicity
//   p: prime
long[] modRoots2(long f0, long f1, long p)
in {
  assert(2 <= p && p < 1L << 31, "modRoots2: 2 <= p < 2^31 must hold");
  assert(0 <= f0 && f0 < p, "modRoots2: 0 <= f0 < p must hold");
  assert(0 <= f1 && f1 < p, "modRoots2: 0 <= f1 < p must hold");
}
do {
  import std.algorithm : sort;
  if (p == 2) {
    if (f0 == 0 && f1 == 0) return [0, 0];
    if (f0 == 0 && f1 == 1) return [0, 1];
    if (f0 == 1 && f1 == 0) return [1, 1];
    return [];
  } else {
    const f12 = f1.div2(p);
    auto ts = modSqrt(f12 * f12 - f0, p);
    foreach (ref t; ts) {
      if ((t -= f12) < 0) t += p;
    }
    sort(ts);
    switch (ts.length) {
      case 0: return [];
      case 1: return [ts[0], ts[0]];
      case 2: return ts;
      default: assert(false);
    }
  }
}

// Roots of f0 + f1 T + f2 T^2 + T^3 in F_p[T] with multiplicity
//   p: prime
long[] modRoots3(long f0, long f1, long f2, long p)
in {
  assert(2 <= p && p <= 1_500_000_001,
         "modRoots3: 2 <= p <= 1_500_000_001 must hold");
  assert(0 <= f0 && f0 < p, "modRoots3: 0 <= f0 < p must hold");
  assert(0 <= f1 && f1 < p, "modRoots3: 0 <= f1 < p must hold");
  assert(0 <= f2 && f2 < p, "modRoots3: 0 <= f2 < p must hold");
}
do {
  import std.algorithm : sort;
  if (p == 2) {
    if (f0 == 0 && f1 == 0 && f2 == 0) return [0, 0, 0];
    if (f0 == 0 && f1 == 0 && f2 == 1) return [0, 0, 1];
    if (f0 == 0 && f1 == 1 && f2 == 0) return [0, 1, 1];
    if (f0 == 1 && f1 == 1 && f2 == 1) return [1, 1, 1];
    if (f0 == 0) return [0];
    if ((f0 + f1 + f2 + 1) % 2 == 0) return [1];
    return [];
  } else if (p == 3) {
    if (f0 == 0 && f1 == 0 && f2 == 0) return [0, 0, 0];
    if (f0 == 0 && f1 == 0 && f2 == 2) return [0, 0, 1];
    if (f0 == 0 && f1 == 0 && f2 == 1) return [0, 0, 2];
    if (f0 == 0 && f1 == 1 && f2 == 1) return [0, 1, 1];
    if (f0 == 0 && f1 == 2 && f2 == 0) return [0, 1, 2];
    if (f0 == 0 && f1 == 1 && f2 == 2) return [0, 2, 2];
    if (f0 == 2 && f1 == 0 && f2 == 0) return [1, 1, 1];
    if (f0 == 1 && f1 == 2 && f2 == 2) return [1, 1, 2];
    if (f0 == 2 && f1 == 2 && f2 == 1) return [1, 2, 2];
    if (f0 == 1 && f1 == 0 && f2 == 0) return [2, 2, 2];
    if (f0 == 0) return [0];
    if ((f0 + f1 + f2 + 1) % 3 == 0) return [1];
    if ((f0 - f1 + f2 - 1) % 3 == 0) return [2];
    return [];
  } else {
    // gcd(f0 + f1 T + f2 T^2 + T^3, f1 + 2 f2 T + 3 T^2)
    //   remainder: (f0 - f1 f2 / 9) + (2 f1 / 3 - 2 f2^2 / 9) T
    const f13 = f1.div3(p), f23 = f2.div3(p);
    long a0 = (f0 - f13 * f23) % p, a1 = (2 * f13 - 2 * f23 * f23) % p;
    if (a0 < 0) a0 += p;
    if (a1 < 0) a1 += p;
    if (a1 != 0) {
      if ((f13 * ((a1 * a1) % p) - 2 * f23 * ((a0 * a1) % p) + a0 * a0) % p != 0) {
        // gcd = 1
      } else {
        // gcd = a0 + a1 T
        const t2 = ((p - a0) * a1.modInv(p)) % p;
        long t1 = (-f2 - 2 * t2) % p;
        if (t1 < 0) t1 += p;
        auto ts = [t1, t2, t2];
        sort(ts);
        return ts;
      }
    } else if (a0 != 0) {
      // gcd = 1
    } else {
      // gcd = f1 + 2 f2 T + 3 T^2
      const t = (f23 != 0) ? (p - f23) : 0;
      return [t, t, t];
    }

    long[3] mul(in long[3] a, in long[3] b) {
      long[3] c = [a[0] * b[0], a[0] * b[1] + a[1] * b[0],
                a[0] * b[2] + a[1] * b[1] + a[2] * b[0]];
      long c3 = a[1] * b[2] + a[2] * b[1], c4 = a[2] * b[2];
      c4 %= p;
      c[1] -= f0 * c4; c[2] -= f1 * c4; c3 -= f2 * c4;
      c3 %= p;
      c[0] -= f0 * c3; c[1] -= f1 * c3; c[2] -= f2 * c3;
      if ((c[0] %= p) < 0) c[0] += p;
      if ((c[1] %= p) < 0) c[1] += p;
      if ((c[2] %= p) < 0) c[2] += p;
      return c;
    }

    // f: square-free
    // gcd(f, T^p - T)
    long[3] t2 = [0, 1, 0], tp = [1, 0, 0];
    for (long e = p; e; e >>= 1) {
      if (e & 1) tp = mul(tp, t2);
      t2 = mul(t2, t2);
    }
    if (--tp[1] < 0) tp[1] += p;
    if (tp[2] != 0) {
      const invTp2 = tp[2].modInv(p);
      (tp[0] *= invTp2) %= p;
      (tp[1] *= invTp2) %= p;
      long b0 = (f0 - (f2 - tp[1]) * tp[0]) % p;
      long b1 = (f1 - tp[0] - (f2 - tp[1]) * tp[1]) % p;
      if (b0 < 0) b0 += p;
      if (b1 < 0) b1 += p;
      if (b1 != 0) {
        if ((tp[0] * ((b1 * b1) % p) - tp[1] * ((b0 * b1) % p) + b0 * b0) % p != 0) {
          // gcd = 1
          return [];
        } else {
          // gcd = b0 + b1 T
          return [((p - b0) * b1.modInv(p)) % p];
        }
      } else if (b0 != 0) {
        // gcd = 1
        return [];
      } else {
        // gcd = tp[0] + tp[1] T + T^2
        assert(false);
      }
    } else if (tp[1] != 0) {
      const tp02 = (tp[0] * tp[0]) % p, tp12 = (tp[1] * tp[1]) % p;
      if ((((f0 * tp[1] - f1 * tp[0]) % p) * tp12 +
           ((f2 * tp[1] - tp[0]) % p) * tp02) % p != 0) {
        // gcd = 1
        return [];
      } else {
        // gcd = tp[0] + tp[1] T
        return [((p - tp[0]) * tp[1].modInv(p)) % p];
      }
    } else if (tp[0] != 0) {
      // gcd = 1
      return [];
    } else {
      // gcd = f0 + f1 T + f2 T^2 + T^3
    }

    // f: split
    for (; ; ) {
      // gcd(rand^((p-1)/2) - 1, f)
      long[3] r2 = [xrand() % p, xrand() % p, xrand() % p], rp = [1, 0, 0];
      for (long e = (p - 1) / 2; e; e >>= 1) {
        if (e & 1) rp = mul(rp, r2);
        r2 = mul(r2, r2);
      }
      if (--rp[0] < 0) rp[0] += p;
      if (rp[2] != 0) {
        const invRp2 = rp[2].modInv(p);
        (rp[0] *= invRp2) %= p;
        (rp[1] *= invRp2) %= p;
        long c0 = (f0 - (f2 - rp[1]) * rp[0]) % p;
        long c1 = (f1 - rp[0] - (f2 - rp[1]) * rp[1]) % p;
        if (c0 < 0) c0 += p;
        if (c1 < 0) c1 += p;
        if (c1 != 0) {
          if ((rp[0] * ((c1 * c1) % p) - rp[1] * ((c0 * c1) % p) + c0 * c0) % p != 0) {
            // gcd = 1
          } else {
            // gcd = c0 + c1 T
            const t = ((p - c0) * c1.modInv(p)) % p;
            auto ts = [t] ~ modRoots2((f1 + (f2 + t) * t) % p, (f2 + t) % p, p);
            sort(ts);
            return ts;
          }
        } else if (c0 != 0) {
          // gcd = 1
        } else {
          // gcd = rp[0] + rp[1] T + T^2
          auto ts = modRoots2(rp[0], rp[1], p) ~ [(rp[1] - f2 + p) % p];
          sort(ts);
          return ts;
        }
      } else if (rp[1] != 0) {
        const rp02 = (rp[0] * rp[0]) % p, rp12 = (rp[1] * rp[1]) % p;
        if ((((f0 * rp[1] - f1 * rp[0]) % p) * rp12 +
             ((f2 * rp[1] - rp[0]) % p) * rp02) % p != 0) {
          // gcd = 1
        } else {
          // gcd = rp[0] + rp[1] T
          const t = ((p - rp[0]) * rp[1].modInv(p)) % p;
          auto ts = [t] ~ modRoots2((f1 + (f2 + t) * t) % p, (f2 + t) % p, p);
          sort(ts);
          return ts;
        }
      } else if (rp[0] != 0) {
        // gcd = 1
      } else {
        // gcd = f0 + f1 T + f2 T^2 + T^3
      }
    }
  }
}

// div2, div3
unittest {
  foreach (m; 1 .. 20) {
    if (m % 2 != 0) {
      foreach (a; 0 .. m) {
        const res = a.div2(m);
        assert(0 <= res && res < m);
        assert((2 * res) % m == a);
      }
    }
  }
  foreach (m; 1 .. 20) {
    if (m % 3 != 0) {
      foreach (a; 0 .. m) {
        const res = a.div3(m);
        assert(0 <= res && res < m);
        assert((3 * res) % m == a);
      }
    }
  }
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
  foreach (p; [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]) {
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

// modRoots2
unittest {
  assert(modRoots2(1, 4, 5) == []);
  assert(modRoots2(4, 4, 5) == [3, 3]);
  assert(modRoots2(2, 3, 5) == [3, 4]);
  assert(modRoots2(123456789, 987654321, 2147483647) == []);
  assert(modRoots2(313032706, 150994941, 2147483647) == [998244353, 998244353]);
  assert(modRoots2(350663538, 1561496200, 2147483647) == [271828182, 314159265]);
  foreach (p; [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]) {
    foreach (f0; 0 .. p) foreach (f1; 0 .. p) {
      long[] ts;
      foreach (t; 0 .. p) {
        if ((f0 + f1 * t + t * t) % p == 0) {
          ts ~= t;
        }
      }
      if (ts.length == 1) {
        ts = [ts[0], ts[0]];
      }
      assert(modRoots2(f0, f1, p) == ts);
    }
  }
}

// modRoot3
unittest {
import std.stdio;
  assert(modRoots3(1, 3, 4, 5) == []);
  assert(modRoots3(2, 3, 2, 5) == [4]);
  assert(modRoots3(2, 2, 4, 5) == [2, 2, 2]);
  assert(modRoots3(4, 0, 2, 5) == [2, 2, 4]);
  assert(modRoots3(1, 1, 1, 5) == [2, 3, 4]);
  assert(modRoots3(135792468, 975318642, 546372819, 1_500_000_001) == []);
  assert(modRoots3(314159265, 358979323, 846264338, 1_500_000_001) == [546438164]);
  assert(modRoots3(1177926947, 999436649, 1439427532, 1_500_000_001) ==
         [20190823, 20190823, 20190823]);
  assert(modRoots3(1055555222, 500000146, 1499999980, 1_500_000_001) ==
         [1000000007, 1000000007, 1000000009]);
  assert(modRoots3(1499999995, 11, 1499999995, 1_500_000_001) == [1, 2, 3]);
  foreach (p; [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]) {
    foreach (f0; 0 .. p) foreach (f1; 0 .. p) foreach (f2; 0 .. p) {
      const res = modRoots3(f0, f1, f2, p);
      if (res.length == 3) {
        assert(res[0] <= res[1] && res[1] <= res[2]);
        assert((res[0] * res[1] * res[2]) % p == (-f0 + p) % p);
        assert((res[0] * res[1] + res[0] * res[2] + res[1] * res[2]) % p == f1);
        assert((res[0] + res[1] + res[2]) % p == (-f2 + p) % p);
      } else {
        long[] ts;
        foreach (t; 0 .. p) {
          if ((f0 + f1 * t + f2 * t * t + t * t * t) % p == 0) {
            ts ~= t;
          }
        }
        assert(res == ts);
      }
    }
  }
}

void main() {
}
