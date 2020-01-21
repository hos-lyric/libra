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

// get([N / j]) = 1 + \sum_{p<[N/j]} p^K
//   O(N^(3/4) / log N) time, O(N^(1/2)) space
class PrimeSum(T, int K) {
  long N, sqrtN;
  bool[] isPrime;
  T[] small, large;
  this(long N) {
    this.N = N;
    sqrtN = floorSqrt(N);
    isPrime = new bool[sqrtN + 1];
    small = new T[sqrtN + 1];
    large = new T[sqrtN + 1];
    isPrime[2 .. $] = true;
    T powerSum(long n) {
      static if (K == 0) {
        return n;
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
        static assert(false, "K is out of range");
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
  }
  T get(long n) {
    return (n <= sqrtN) ? small[n] : large[N / n];
  }
}

// get([N / j]) = 1 + \sum_{p<[N/j]} p^K
//   O(N^(3/4) / log N) time, O(N^(1/2)) space
//   large K; \sum_{i=1}^n i^K = \sum_{j=1}^{K+1} coef[j] n^j
class PrimeSum(T) {
  long N, sqrtN;
  bool[] isPrime;
  T[] small, large;
  this(long N, int K, T[] coef) {
    this.N = N;
    sqrtN = floorSqrt(N);
    isPrime = new bool[sqrtN + 1];
    small = new T[sqrtN + 1];
    large = new T[sqrtN + 1];
    isPrime[2 .. $] = true;
    T powerSum(long n) {
      T y;
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
  }
  T get(long n) {
    return (n <= sqrtN) ? small[n] : large[N / n];
  }
}


import std.conv : to;
struct ModInt(int M_) {
  alias M = M_;
  int x;
  this(ModInt a) { x = a.x; }
  this(long a) { x = cast(int)(a % M); if (x < 0) x += M; }
  ref ModInt opAssign(long a) { return (this = ModInt(a)); }
  ref ModInt opOpAssign(string op)(ModInt a) {
    static if (op == "+") { x += a.x; if (x >= M) x -= M; }
    else static if (op == "-") { x -= a.x; if (x < 0) x += M; }
    else static if (op == "*") { x = cast(int)((cast(long)(x) * a.x) % M); }
    else static if (op == "/") { this *= a.inv(); }
    else static assert(false);
    return this;
  }
  ref ModInt opOpAssign(string op)(long a) {
    static if (op == "^^") {
      ModInt t2 = this, te = ModInt(1);
      for (long e = a; e; e >>= 1) {
        if (e & 1) te *= t2;
        t2 *= t2;
      }
      x = cast(int)(te.x);
      return this;
    } else return mixin("this " ~ op ~ "= ModInt(a)");
  }
  ModInt inv() const {
    int a = x, b = M, y = 1, z = 0, t;
    for (; ; ) {
      t = a / b; a -= t * b;
      if (a == 0) {
        assert(b == 1 || b == -1);
        return ModInt(b * z);
      }
      y -= t * z;
      t = b / a; b -= t * a;
      if (b == 0) {
        assert(a == 1 || a == -1);
        return ModInt(a * y);
      }
      z -= t * y;
    }
  }
  ModInt opUnary(string op)() const if (op == "-") { return ModInt(-x); }
  ModInt opBinary(string op, T)(T a) const { return mixin("ModInt(this) " ~ op ~ "= a"); }
  ModInt opBinaryRight(string op)(long a) const { return mixin("ModInt(a) " ~ op ~ "= this"); }
  string toString() const { return x.to!string; }
}

unittest {
  auto ps0 = new PrimeSum!(long, 0)(10L^^10);
  assert(ps0.get(10L^^10) == 1 + 455052511);
  assert(ps0.get(10L^^9) == 1 + 50847534);
  auto ps1 = new PrimeSum!(long, 1)(121);
  assert(ps1.small == [0, 1, 3, 6, 6, 11, 11, 18, 18, 18, 18, 29]);
  assert(ps1.large == [0, 1594, 441, 198, 130, 101, 78, 59, 42, 42, 29, 29]);
  assert(new PrimeSum!(long, 0)(10L^^5).get(10L^^5) == 9593);
  assert(new PrimeSum!(long, 1)(10L^^5).get(10L^^5) == 454396538);
  assert(new PrimeSum!(long, 2)(10L^^5).get(10L^^5) == 29822760083884L);
  assert(new PrimeSum!(long, 3)(10L^^5).get(10L^^5) == 2220319074671146688L);

  alias Mint = ModInt!998244353;
  assert(new PrimeSum!(Mint, 3)(10L^^5).get(10L^^5).x == 909721510);
  auto ps4 = new PrimeSum!(Mint)(10L^^5, 4,
      [Mint(0), -Mint(30).inv, Mint(0), Mint(3).inv, Mint(2).inv, Mint(5).inv]);
  assert(ps4.get(10L^^5).x == 172030739);
  assert(ps4.get(33333).x == 796721800);
}

void main() {
}
