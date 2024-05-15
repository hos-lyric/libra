import modint;

// floor(sqrt(a))
long floorSqrt(long a) {
  import core.bitop : bsr;
  import std.algorithm : min;
  long b = a, x = 0, y = 0;
  for (int e = bsr(a) & ~1; e >= 0; e -= 2) {
    x <<= 1;
    y <<= 1;
    if (b >= (y | 1) << e) {
      b -= (y | 1) << e;
      x |= 1;
      y += 2;
    }
  }
  return x;
}

// get(floor(N / l)) = \sum_{p<=floor(N/l)} p^K
//   O(N^(3/4) / log N) time, O(N^(1/2)) space
class PrimeSum(T, int K) {
  long N, sqrtN;
  bool[] isPrime;
  T[] small, large;
  this(long N) {
    assert(N >= 1, "PrimeSum: N >= 1 must hold");
    this.N = N;
    sqrtN = floorSqrt(N);
    isPrime = new bool[sqrtN + 1];
    small = new T[sqrtN + 1];
    large = new T[sqrtN + 1];
    isPrime[2 .. $] = true;
    T powerSum(long n) {
      static if (K == 0) {
        return T(n);
      } else static if (K == 1) {
        long n0 = n, n1 = n + 1;
        ((n0 % 2 == 0) ? n0 : n1) /= 2;
        return T(n0) * T(n1);
      } else static if (K == 2) {
        long n0 = n, n1 = n + 1, n2 = 2 * n + 1;
        ((n0 % 2 == 0) ? n0 : n1) /= 2;
        ((n0 % 3 == 0) ? n0 : (n1 % 3 == 0) ? n1 : n2) /= 3;
        return T(n0) * T(n1) * T(n2);
      } else static if (K == 3) {
        long n0 = n, n1 = n + 1;
        ((n0 % 2 == 0) ? n0 : n1) /= 2;
        return T(n0) * T(n0) * T(n1) * T(n1);
      } else {
        static assert(false, "PrimeSum: K is out of range");
      }
    }
    foreach (n; 1 .. sqrtN + 1) small[n] = powerSum(n);
    foreach (l; 1 .. sqrtN + 1) large[l] = powerSum(N / l);
    foreach (p; 2 .. sqrtN + 1) {
      if (isPrime[p]) {
        for (long n = p^^2; n <= sqrtN; n += p) isPrime[n] = false;
        const pk = T(p)^^K, g1 = get(p - 1);
        foreach (l; 1 .. sqrtN + 1) {
          const n = N / l;
          if (n < p^^2) break;
          large[l] -= pk * (get(n / p) - g1);
        }
        foreach_reverse (n; 1 .. sqrtN + 1) {
          if (n < p^^2) break;
          small[n] -= pk * (get(n / p) - g1);
        }
      }
    }
    small[1 .. $] -= T(1);
    large[1 .. $] -= T(1);
  }
  T get(long n) const {
    return (n <= sqrtN) ? small[n] : large[N / n];
  }
}

// get(floor(N / l)) = \sum_{p<=floor(N/l)} p^K
//   O(N^(3/4) / log N) time, O(N^(1/2)) space
//   large K; \sum_{i=1}^n i^K = \sum_{j=1}^{K+1} coef[j] n^j
class PrimeSum(T) {
  long N, sqrtN;
  bool[] isPrime;
  T[] small, large;
  this(long N, int K, T[] coef) {
    assert(N >= 1, "PrimeSum: N >= 1 must hold");
    this.N = N;
    sqrtN = floorSqrt(N);
    isPrime = new bool[sqrtN + 1];
    small = new T[sqrtN + 1];
    large = new T[sqrtN + 1];
    isPrime[2 .. $] = true;
    T powerSum(long n) {
      T y = 0;
      foreach_reverse (k; 1 .. K + 2) (y += coef[k]) *= n;
      return y;
    }
    foreach (n; 1 .. sqrtN + 1) small[n] = powerSum(n);
    foreach (l; 1 .. sqrtN + 1) large[l] = powerSum(N / l);
    foreach (p; 2 .. sqrtN + 1) {
      if (isPrime[p]) {
        for (long n = p^^2; n <= sqrtN; n += p) isPrime[n] = false;
        const pk = T(p)^^K, g1 = get(p - 1);
        foreach (l; 1 .. sqrtN + 1) {
          const n = N / l;
          if (n < p^^2) break;
          large[l] -= pk * (get(n / p) - g1);
        }
        foreach_reverse (n; 1 .. sqrtN + 1) {
          if (n < p^^2) break;
          small[n] -= pk * (get(n / p) - g1);
        }
      }
    }
    small[1 .. $] -= T(1);
    large[1 .. $] -= T(1);
  }
  T get(long n) const {
    return (n <= sqrtN) ? small[n] : large[N / n];
  }
}

// get(floor(N / l)) = \sum_{n=1}^{floor(N/l)} f(n)
//   O(N^(3/4) / log N) time, O(N^(1/2)) space
//   f: multiplicative function, f(p): poly in p
class MultiplicativeSum(T) {
  long N, sqrtN;
  bool[] isPrime;
  T[] smallFP, small, large;
  this(long N) {
    assert(N >= 1, "PrimeSum: N >= 1 must hold");
    this.N = N;
    sqrtN = floorSqrt(N);
    isPrime = new bool[sqrtN + 1];
    smallFP = new T[sqrtN + 1];
    small = new T[sqrtN + 1];
    large = new T[sqrtN + 1];
    isPrime[2 .. $] = true;
    foreach (p; 2 .. sqrtN + 1) {
      if (isPrime[p]) {
        for (long n = p^^2; n <= sqrtN; n += p) isPrime[n] = false;
      }
    }
  }
  // prepare \sum_{p<=n} f(p) and \sum_{N^(1/2)<p<=floor(N/l)} f(p)
  void add(S)(T coef, S primeSum) {
    assert(N == primeSum.N, "MultiplicativeSum: N must agree");
    foreach (n; 1 .. sqrtN + 1) smallFP[n] += coef * primeSum.small[n];
    foreach (l; 1 .. sqrtN + 1) {
      large[l] += coef * (primeSum.large[l] - primeSum.small[sqrtN]);
    }
  }
  // (p, e) -> f(p^e)
  void build(T delegate(long, int) f) {
    import std.algorithm : max;
    small[1 .. $] += T(1);
    large[1 .. $] += T(1);
    foreach_reverse (p; 2 .. sqrtN + 1) {
      if (isPrime[p]) {
        // added f(p') for p < p' <= min{n, N^(1/2)}
        T getAdded(long n) const {
          return (n <= sqrtN) ? (small[n] + smallFP[max(n, p)] - smallFP[p])
                              : (large[N / n] + smallFP[sqrtN] - smallFP[p]);
        }
        // p^e, f(p^e)
        long[] pes = [1];
        T[] fs = [T(1)];
        long pe = p;
        for (int e = 1; ; ++e) {
          pes ~= pe;
          fs ~= f(p, e);
          if (pe > N / p) break;
          pe *= p;
        }
        const limE = cast(int)(pes.length);
        foreach (l; 1 .. sqrtN + 1) {
          const n = N / l;
          if (n < p^^2) break;
          for (int e = 1; e < limE && pes[e] <= n; ++e) {
            large[l] += fs[e] * getAdded(n / pes[e]);
          }
          large[l] -= fs[1];
        }
        foreach_reverse (n; 1 .. sqrtN + 1) {
          if (n < p^^2) break;
          for (int e = 1; e < limE && pes[e] <= n; ++e) {
            small[n] += fs[e] * getAdded(n / pes[e]);
          }
          small[n] -= fs[1];
        }
      }
    }
    small[] += smallFP[];
    large[1 .. $] += smallFP[sqrtN];
  }
  T get(long n) const {
    return (n <= sqrtN) ? small[n] : large[N / n];
  }
}

// PrimeSum
unittest {
  assert(new PrimeSum!(long, 0)(1).get(1) == 0);
  assert(new PrimeSum!(long, 0)(2).get(2) == 1);
  assert(new PrimeSum!(long, 0)(3).get(3) == 2);
  assert(new PrimeSum!(long, 0)(4).get(4) == 2);
  {
    auto ps = new PrimeSum!(long, 0)(10L^^10);
    assert(ps.get(10L^^10) == 455052511);
    assert(ps.get(10L^^9) == 50847534);
  }
  {
    auto ps = new PrimeSum!(long, 1)(100);
    assert(ps.small == [0, 0, 2, 5, 5, 10, 10, 17, 17, 17, 17]);
    assert(ps.large == [0, 1060, 328, 160, 100, 77, 41, 41, 28, 28, 17]);
  }
  {
    auto ps = new PrimeSum!(long, 1)(120);
    assert(ps.small == [0, 0, 2, 5, 5, 10, 10, 17, 17, 17, 17]);
    assert(ps.large == [0, 1593, 440, 197, 129, 100, 77, 58, 41, 41, 28]);
  }
  assert(new PrimeSum!(long, 0)(10L^^5).get(10L^^5) == 9592);
  assert(new PrimeSum!(long, 1)(10L^^5).get(10L^^5) == 454396537);
  assert(new PrimeSum!(long, 2)(10L^^5).get(10L^^5) == 29822760083883L);
  assert(new PrimeSum!(long, 3)(10L^^5).get(10L^^5) == 2220319074671146687L);

  assert(new PrimeSum!(ModInt!(2^^29), 3)(10L^^5).get(10L^^5).x == 97269439);
  {
    alias Mint = ModInt!998244353;
    auto ps = new PrimeSum!(Mint)(10L^^5, 4,
        [Mint(0), -Mint(30).inv, Mint(0), Mint(3).inv, Mint(2).inv, Mint(5).inv]);
    assert(ps.get(10L^^5).x == 172030738);
    assert(ps.get(33333).x == 796721799);
  }
}

// MultiplicativeSum
unittest {
  // \phi
  {
    auto ms = new MultiplicativeSum!long(100);
    ms.add(-1, new PrimeSum!(long, 0)(100));
    ms.add(1, new PrimeSum!(long, 1)(100));
    ms.build((p, e) => p^^(e - 1) * (p - 1));
    assert(ms.small == [0, 1, 2, 4, 6, 10, 12, 18, 22, 28, 32]);
    assert(ms.large == [0, 3044, 774, 344, 200, 128, 80, 64, 46, 42, 32]);
  }
  {
    auto ms = new MultiplicativeSum!long(120);
    ms.add(-1, new PrimeSum!(long, 0)(120));
    ms.add(1, new PrimeSum!(long, 1)(120));
    ms.build((p, e) => p^^(e - 1) * (p - 1));
    assert(ms.small == [0, 1, 2, 4, 6, 10, 12, 18, 22, 28, 32]);
    assert(ms.large == [0, 4386, 1102, 490, 278, 180, 128, 96, 72, 58, 46]);
  }

  // \sigma_1
  {
    import std.algorithm : map, sum;
    import std.range : iota;
    auto ms = new MultiplicativeSum!long(10L^^6);
    ms.add(1, new PrimeSum!(long, 0)(10L^^6));
    ms.add(1, new PrimeSum!(long, 1)(10L^^6));
    ms.build((p, e) => iota(e + 1).map!(f => p^^f).sum);
    assert(ms.get(10L^^6) == 822468118437L);
  }
  {
    import std.algorithm : map, sum;
    import std.range : iota;
    alias Mint = ModInt!(10^^9);
    auto ms = new MultiplicativeSum!Mint(10L^^6);
    ms.add(Mint(1), new PrimeSum!(Mint, 0)(10L^^6));
    ms.add(Mint(1), new PrimeSum!(Mint, 1)(10L^^6));
    ms.build((p, e) => iota(e + 1).map!(f => Mint(p)^^f).sum);
    assert(ms.get(10L^^6).x == 468118437);
  }
}

void main() {
}
