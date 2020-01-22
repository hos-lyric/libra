// ModInt
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

// Pretty print (smaller abs)
int[] pretty(int M)(ModInt!M[] as) {
  import std.algorithm : map;
  import std.array : array;
  return as.map!(a => (a.x < M - a.x) ? a.x : -(M - a.x)).array;
}

// Berlekamp-Massey
//   as[i] + \sum_{j=1}^l cs[j] as[i - j] = 0
//   M must be prime
ModInt!M[] findLinearRecurrence(int M)(ModInt!M[] as) {
  import std.algorithm : min;
  const n = cast(int)(as.length);
  int l, m;
  auto cs = new ModInt!M[n + 1], bs = new ModInt!M[n + 1];
  cs[0] = bs[0] = 1;
  ModInt!M bef = 1;
  foreach (i; 0 .. n) {
    ++m;
    ModInt!M dif = as[i];
    foreach (j; 1 .. l + 1) dif += cs[j] * as[i - j];
    if (dif.x != 0) {
      auto csDup = cs.dup;
      const r = dif / bef;
      foreach (j; m .. n) cs[j] -= r * bs[j - m];
      if (2 * l <= i) {
        l = i + 1 - l;
        m = 0;
        bs = csDup;
        bef = dif;
      }
    }
  }
  return cs[0 .. l + 1];
}

ModInt!M[] findLinearRecurrence(int M)(long[] as) {
  import std.algorithm : map;
  import std.array : array;
  return findLinearRecurrence(as.map!(a => ModInt!M(a)).array);
}

unittest {
  enum MO = 998244353;
  assert([1, -3, 2] == findLinearRecurrence!MO([3, 4, 6, 10]).pretty);
  assert([1, -3, 2] == findLinearRecurrence!MO([3, 4, 6, 10, 18, 34]).pretty);
  assert([1, 3, 0, -39, 36] ==
         findLinearRecurrence!MO([3, 4, 6, 10, 18, 36, 66, 144]).pretty);
  assert([1] == findLinearRecurrence!MO(new long[0]).pretty);
  assert([1] == findLinearRecurrence!MO([0]).pretty);
  assert([1, 0] == findLinearRecurrence!MO([1]).pretty);
  assert([1, 0, 0, 0, 0] ==
         findLinearRecurrence!MO([1, 2, 4, 8, 0, 0, 0, 0]).pretty);
  assert([1] == findLinearRecurrence!MO([0, 0, 0, 0, 0]).pretty);
  assert([1, 0, 0, 0, 0, 0] == findLinearRecurrence!MO([0, 0, 0, 0, 1]).pretty);
}

void main() {
}
