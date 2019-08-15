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

// Polynomial f = f[0] + f[1] T + f[2] T^2 + ... + f[d] T^d

// Remove extra leading zeros from f
long[] polyChomp(in long[] f)
in {
  assert(f != [], "polyChomp: f must not be empty");
}
do {
  foreach_reverse (i; 0 .. f.length) {
    if (f[i] != 0) return f[0 .. i + 1].dup;
  }
  return [0];
}

// Derivative of f in (Z/mZ)[T]
long[] polyDerivative(in long[] f, long m)
in {
  assert(f != [], "polyDerivative: f must not be empty");
  assert(1 <= m && m <= 0x7fffffff, "polyMod: 1 <= m < 2^31 must hold");
  foreach (a; f) {
    assert(0 <= a && a < m,
           "polyDerivative: coefficients of f must be in [0, m)");
  }
  assert(f == [0] || f[$ - 1] != 0, "polyDerivative: extra leading zero in f");
}
do {
  const d = cast(int)(f.length) - 1;
  if (d == 0) {
    return [0];
  } else {
    auto b = new long[d];
    foreach (i; 1 .. d + 1) {
      b[i - 1] = (i * f[i]) % m;
    }
    return b.polyChomp();
  }
}

// f g in (Z/mZ)[T]
long[] polyMul(in long[] f, in long[] g, long m)
in {
  assert(f != [], "polyDivMod: f must not be empty");
  assert(g != [], "polyDivMod: g must not be empty");
  assert(2 <= m && m <= 0x7fffffff, "polyDivMod: 2 <= m < 2^31 must hold");
  foreach (a; f) {
    assert(0 <= a && a < m, "polyDivMod: coefficients of f must be in [0, m)");
  }
  foreach (a; g) {
    assert(0 <= a && a < m, "polyDivMod: coefficients of g must be in [0, m)");
  }
  assert(f == [0] || f[$ - 1] != 0, "polyDivMod: extra leading zero in f");
  assert(g == [0] || g[$ - 1] != 0, "polyDivMod: extra leading zero in g");
}
do {
  if (f == [0] || g == [0]) return [0];
  const d = cast(int)(f.length) - 1;
  const e = cast(int)(g.length) - 1;
  auto h = new long[d + e + 1];
  foreach (i; 0 .. d + 1) foreach (j; 0 .. e + 1) {
    (h[i + j] += f[i] * g[j]) %= m;
  }
  return h;
}

// f divided by g in (Z/mZ)[T]
long[] polyDivMod(string op)(in long[] f, in long[] g, long m)
in {
  assert(f != [], "polyDivMod: f must not be empty");
  assert(g != [], "polyDivMod: g must not be empty");
  assert(2 <= m && m <= 0x7fffffff, "polyDivMod: 2 <= m < 2^31 must hold");
  foreach (a; f) {
    assert(0 <= a && a < m, "polyDivMod: coefficients of f must be in [0, m)");
  }
  foreach (a; g) {
    assert(0 <= a && a < m, "polyDivMod: coefficients of g must be in [0, m)");
  }
  assert(f == [0] || f[$ - 1] != 0, "polyDivMod: extra leading zero in f");
  assert(g == [0] || g[$ - 1] != 0, "polyDivMod: extra leading zero in g");
  assert(g[$ - 1] == 1, "polyDivMod: g must be monic");
}
do {
  const d = cast(int)(f.length) - 1;
  const e = cast(int)(g.length) - 1;
  if (d < e) {
    static if (op == "/") {
      return [0];
    } else static if (op == "%") {
      return f.dup;
    } else {
      static assert(false);
    }
  } else {
    auto q = new long[d - e + 1], r = f.dup;
    foreach_reverse (i; 0 .. d - e + 1) {
      q[i] = r[i + e];
      foreach (j; 0 .. e + 1) {
        if (((r[i + j] -= q[i] * g[j]) %= m) < 0) r[i + j] += m;
      }
    }
    static if (op == "/") {
      return q;
    } else static if (op == "%") {
      return r.polyChomp();
    } else {
      static assert(false);
    }
  }
}

// gcd(f, g) in F_p[T]
//   p: prime
long[] polyGcd(in long[] f, in long[] g, long p)
in {
  assert(f != [], "polyGcd: f must not be empty");
  assert(g != [], "polyGcd: g must not be empty");
  assert(2 <= p && p <= 0x7fffffff, "polyGcd: 2 <= p < 2^31 must hold");
  foreach (a; f) {
    assert(0 <= a && a < p, "polyGcd: coefficients of f must be in [0, p)");
  }
  foreach (a; g) {
    assert(0 <= a && a < p, "polyGcd: coefficients of g must be in [0, p)");
  }
  assert(f == [0] || f[$ - 1] != 0, "polyGcd: extra leading zero in f");
  assert(g == [0] || g[$ - 1] != 0, "polyGcd: extra leading zero in g");
}
do {
  auto ff = f.dup, gg = g.dup;
  long t;
  if (gg == [0]) {
    t = modInv(ff[$ - 1], p);
    foreach (ref a; ff) (a *= t) %= p;
    return ff;
  }
  for (; ; ) {
    t = modInv(gg[$ - 1], p);
    foreach (ref a; gg) (a *= t) %= p;
    ff = ff.polyDivMod!"%"(gg, p);
    if (ff == [0]) return gg;
    t = modInv(ff[$ - 1], p);
    foreach (ref a; ff) (a *= t) %= p;
    gg = gg.polyDivMod!"%"(ff, p);
    if (gg == [0]) return ff;
  }
}

// T^(pi) mod f in F_p[T] (0 <= i < deg f)
//   Note that g -> g^p is linear
long[][] polyPthPowerMod(in long[] f, long p)
in {
  assert(f.length >= 2, "polyFactorize: deg f >= 1 must hold");
  assert(2 <= p && p <= 0x7fffffff, "polyGcd: 2 <= p < 2^31 must hold");
  foreach (a; f) {
    assert(0 <= a && a < p, "polyFactorize: coefficients of f must be in [0, p)");
  }
  assert(f[$ - 1] == 1, "polyFactorize: f must be monic");
}
do {
  const d = cast(int)(f.length) - 1;
  auto coef = new long[][d];
  coef[0] = [1];
  if (d > 1) {
    long[] g = [0, 1];
    coef[1] = [1];
    for (long pp = p; pp; pp >>= 1) {
      if (pp & 1) coef[1] = polyMul(coef[1], g, p).polyDivMod!"%"(f, p);
      g = polyMul(g, g, p).polyDivMod!"%"(f, p);
    }
    foreach (i; 2 .. d) {
      coef[i] = polyMul(coef[i - 1], coef[1], p).polyDivMod!"%"(f, p);
    }
  }
  return coef;
}

// Factorize f in F_p[T]
//   p: prime
//   increasing order of multiplicity, increasing order of degree, lex order
import std.typecons : Tuple, tuple;
Tuple!(long[], int)[] polyFactorize(in long[] f, long p)
in {
  assert(f != [], "polyFactorize: f must not be empty");
  assert(2 <= p && p <= 0x7fffffff, "polyGcd: 2 <= p < 2^31 must hold");
  foreach (a; f) {
    assert(0 <= a && a < p, "polyFactorize: coefficients of f must be in [0, p)");
  }
  assert(f[$ - 1] == 1, "polyFactorize: f must be monic");
}
do {
  import std.algorithm : sort;

  int ee;
  long[][] coef;
  long[] pth(long[] h) {
    auto hh = new long[ee];
    foreach (k; 0 .. h.length) foreach (l; 0 .. coef[k].length) {
      (hh[l] += coef[k][l] * h[k]) %= p;
    }
    return hh.polyChomp();
  }

  // square-free factorization
  const d = cast(int)(f.length) - 1;
  auto sff = new long[][d + 1];
  auto ff = f.dup;
  for (int pp = 1; ; pp *= cast(int)(p)) {
    auto g = polyGcd(ff, polyDerivative(ff, p), p);
    ff = polyDivMod!"/"(ff, g, p);
    for (int i = 1; ff != [1]; ++i) {
      auto h = polyGcd(ff, g, p);
      sff[pp * i] = polyDivMod!"/"(ff, h, p);
      ff = h;
      g = polyDivMod!"/"(g, h, p);
    }
    if (g == [1]) break;
    const e = (cast(int)(g.length) - 1) / cast(int)(p);
    ff = new long[e + 1];
    foreach (i; 0 .. e + 1) {
      ff[i] = g[cast(int)(p) * i];
    }
  }

  Tuple!(long[], int)[] ans;
  foreach (i; 1 .. d + 1) {
    if (sff[i] != [] && sff[i] != [1]) {
      // distinct-degree factorization
      const e = cast(int)(sff[i].length) - 1;
      auto ddf = new long[][e + 1];
      auto g = sff[i];
      ee = cast(int)(g.length) - 1;
      coef = polyPthPowerMod(g, p);
      long[] tj = [0, 1];
      for (int j = 1; 2 * j <= cast(int)(g.length) - 1; ++j) {
        // gcd(g, T^(p^j) - T)
        tj = pth(tj);
        auto tjt = tj.dup;
        if (tjt.length < 2) tjt.length = 2;
        if (--tjt[1] < 0) tjt[1] += p;
        tjt = tjt.polyChomp();
        ddf[j] = polyGcd(g, tjt, p);
        g = polyDivMod!"/"(g, ddf[j], p);
      }
      if (g != [1]) {
        ddf[cast(int)(g.length) - 1] = g;
      }

      foreach (j; 1 .. e + 1) {
        if (ddf[j] != [] && ddf[j] != [1]) {
          // Cantor-Zassenhaus
          ee = cast(int)(ddf[j].length) - 1;
          coef = polyPthPowerMod(ddf[j], p);
          auto factors = [ddf[j]];
          for (; factors.length < ee / j; ) {
            // random poly of deg < ee
            auto r = new long[ee];
            foreach (k; 0 .. ee) {
              r[k] = xrand() % p;
            }
            r = r.polyChomp();
            long[] rr;
            if (p == 2) {
              // (r + r^2 + r^4 + ... + r^(2^(j-1))) mod ddf[j]
              auto r2 = r;
              rr = new long[ee];
              foreach (_; 0 .. j) {
                foreach (k; 0 .. r2.length) {
                  if ((rr[k] += r2[k]) >= p) rr[k] -= p;
                }
                r2 = pth(r2);
              }
              rr = rr.polyChomp();
            } else {
              // (r^((p^j-1)/2) - 1) mod ddf[j]
              long[] r2 = r, rp = [1];
              rr = [1];
              for (long pp = (p - 1) / 2; pp; pp >>= 1) {
                if (pp & 1) rp = polyMul(rp, r2, p).polyDivMod!"%"(ddf[j], p);
                r2 = polyMul(r2, r2, p).polyDivMod!"%"(ddf[j], p);
              }
              foreach (_; 0 .. j) {
                rr = polyMul(pth(rr), rp, p).polyDivMod!"%"(ddf[j], p);
              }
              if (--rr[0] < 0) rr[0] += p;
            }
            long[][] factorsNext;
            foreach (factor; factors) {
              if (cast(int)(factor.length) - 1 > j) {
                auto h = polyGcd(factor, rr, p);
                if (h != [1] &&
                    cast(int)(h.length) - 1 < cast(int)(factor.length) - 1) {
                  factorsNext ~= h;
                  factorsNext ~= polyDivMod!"/"(factor, h, p);
                } else {
                  factorsNext ~= factor;
                }
              } else {
                factorsNext ~= factor;
              }
            }
            factors = factorsNext;
          }
          sort(factors);
          foreach (factor; factors) {
            ans ~= tuple(factor, i);
          }
        }
      }
    }
  }
  return ans;
}


// polyChomp
unittest {
  assert(polyChomp([0]) == [0]);
  assert(polyChomp([0, 0]) == [0]);
  assert(polyChomp([1]) == [1]);
  assert(polyChomp([1, 0]) == [1]);
  assert(polyChomp([1, -1, 1, -1]) == [1, -1, 1, -1]);
  assert(polyChomp([1, -1, 1, -1, 0, 0]) == [1, -1, 1, -1]);
}

// polyDerivative
unittest {
  assert(polyDerivative([1], 3) == [0]);
  assert(polyDerivative([4, 2, 2, 3, 0, 1, 4], 5) == [2, 4, 4, 0, 0, 4]);
}

// polyMul
unittest {
  assert(polyMul([3, 1, 4], [1, 5, 9, 2], 12) == [3, 4, 0, 11, 2, 8]);
  assert(polyMul([1, 5, 9, 2], [3, 1, 4], 12) == [3, 4, 0, 11, 2, 8]);
}

// polyDivMod
unittest {
  assert(polyDivMod!"/"([98, 3, 4], [93, 2, 87, 1], 100) == [0]);
  assert(polyDivMod!"%"([98, 3, 4], [93, 2, 87, 1], 100) == [98, 3, 4]);
  assert(polyDivMod!"/"([93, 2, 87, 4], [98, 3, 1], 100) == [75, 4]);
  assert(polyDivMod!"%"([93, 2, 87, 4], [98, 3, 1], 100) == [43, 85]);
  assert(polyDivMod!"/"([0, 0, 0, 0, 2], [0, 0, 1], 13) == [0, 0, 2]);
  assert(polyDivMod!"%"([0, 0, 0, 0, 2], [0, 0, 1], 13) == [0]);
  assert(polyDivMod!"/"([0, 0, 1, 1, 0, 1], [1, 1, 1, 1], 3) == [1, 2, 1]);
  assert(polyDivMod!"%"([0, 2, 1, 1, 0, 1], [1, 1, 1, 1], 3) == [2, 2]);
}

// polyGcd
unittest {
  assert(polyGcd([12, 1, 2], [7, 8, 1], 13) == [1, 1]);
  assert(polyGcd([7, 8, 1], [12, 1, 2], 13) == [1, 1]);
  assert(polyGcd([12, 1, 2], [0], 13) == [6, 7, 1]);
  assert(polyGcd([0], [12, 1, 2], 13) == [6, 7, 1]);
  assert(polyGcd([0, 4, 0, 0, 0, 1], [3, 2, 4, 2, 2, 3, 0, 3, 0, 0, 1], 5) ==
         [4, 0, 0, 0, 1]);
  assert(polyGcd([3, 2, 4, 2, 2, 3, 0, 3, 0, 0, 1], [0, 4, 0, 0, 0, 1], 5) ==
         [4, 0, 0, 0, 1]);
}

// polyPthPowerMod
unittest {
  assert(polyPthPowerMod([2, 1], 13) == [[1]]);
  assert(polyPthPowerMod([3, 2, 1], 13) == [[1], [11, 12]]);
  assert(polyPthPowerMod([7, 4, 2, 1], 13) == [[1], [6, 3, 10], [2, 0, 9]]);
}

// polyFactorize
unittest {
  // SFF: (2 + 4 T + 3 T^3 + 3 T^4 + T^5)^1 (3 + 4 T + 4 T^2 + T^3)^2 (4 + T)^10
  // DDF: ((2 + 3 T + T^2) (1 + T + T^3))^1 ((3 + T) (1 + T + T^2))^2 (4 + T)^10
  assert(polyFactorize([3, 3, 1, 4, 2, 3, 0, 1, 0, 2,
                        1, 2, 0, 3, 0, 2, 4, 3, 3, 1, 1, 1], 5) ==
         [tuple([1, 1], 1), tuple([2, 1], 1), tuple([1, 1, 0, 1], 1),
          tuple([3, 1], 2), tuple([1, 1, 1], 2),
          tuple([4, 1], 10)]);

  // SFF: (1 + T + T^2 + T^3 + T^4)^1 (1 + T + T^2 + T^4 + T^5 + T^6 + T^10)^2
  //      (1 + T^3 + T^4 + T^5 + T^6)^3 (T + T^2)^6
  // DDF: (1 + T + T^2 + T^3 + T^4)^1
  //      ((1 + T + T^2 + T^3 + T^4 + T^5 + T^6) (1 + T^3 + T^4))^2
  //      ((1 + T + T^2) (1 + T + T^4))^3 (T + T^2)^6
  assert(polyFactorize([0, 0, 0, 0, 0, 0, 1, 1, 1, 0,
                        0, 0, 1, 0, 0, 1, 0, 1, 0, 0,
                        0, 1, 0, 0, 0, 1, 1, 1, 0, 1,
                        1, 1, 1, 0, 1, 1, 0, 0, 1, 1,
                        1, 1, 0, 0, 1, 0, 1, 0, 0, 1,
                        1, 0, 1, 0, 1], 2) ==
         [tuple([1, 1, 1, 1, 1], 1),
          tuple([1, 0, 1, 1], 2),
          tuple([1, 1, 0, 1], 2),
          tuple([1, 0, 0, 1, 1], 2),
          tuple([1, 1, 1], 3),
          tuple([1, 1, 0, 0, 1], 3),
          tuple([0, 1], 6),
          tuple([1, 1], 6)]);

  assert(polyFactorize([0, 0, 2, 0, 0, 1], 3) ==
         [tuple([0, 1], 2), tuple([2, 1], 3)]);
  assert(polyFactorize([0, 0, 0, 1, 1, 1], 3) ==
         [tuple([2, 1], 2), tuple([0, 1], 3)]);
  assert(polyFactorize([0, 0, 0, 2, 0, 0, 2, 0, 0, 1], 3) ==
         [tuple([0, 1], 3), tuple([2, 2, 1], 3)]);
  assert(polyFactorize([0, 0, 0, 2, 0, 0, 1], 3) ==
         [tuple([0, 1], 3), tuple([2, 1], 3)]);
}

void main() {
}
