// dmd -O -unittest recurrence ../number/modint
import modint;

// Pretty print (smaller abs)
int[] pretty(int M)(ModInt!M[] as) {
  import std.algorithm : map;
  import std.array : array;
  return as.map!(a => (a.x < M - a.x) ? cast(int)(a.x) : -cast(int)(M - a.x)).array;
}
int[] pretty(int M)(const(ModInt!M)[] as) {
  import std.algorithm : map;
  import std.array : array;
  return as.map!(a => (a.x < M - a.x) ? cast(int)(a.x) : -cast(int)(M - a.x)).array;
}

// Berlekamp-Massey
//   F: field
//   \sum_{j=1}^0 cs[j] as[i - j] = 0 (d <= i < |as|), cs[0] = 1
//   M must be prime
F[] findLinearRecurrence(F)(inout(F)[] as) {
  import std.algorithm : min;
  const n = cast(int)(as.length);
  int d, m;
  auto cs = new F[n + 1], bs = new F[n + 1];
  cs[0] = bs[0] = 1;
  F invBef = 1;
  foreach (i; 0 .. n) {
    ++m;
    F dif = as[i];
    foreach (j; 1 .. d + 1) dif += cs[j] * as[i - j];
    if (dif.x != 0) {
      auto csDup = cs.dup;
      const r = dif * invBef;
      foreach (j; m .. n) cs[j] -= r * bs[j - m];
      if (2 * d <= i) {
        d = i + 1 - d;
        m = 0;
        bs = csDup;
        invBef = dif.inv;
      }
    }
  }
  return cs[0 .. d + 1];
}

ModInt!M[] findLinearRecurrence(int M)(long[] as) {
  import std.algorithm : map;
  import std.array : array;
  return findLinearRecurrence(as.map!(a => ModInt!M(a)).array);
}

unittest {
  enum MO = 998244353;
  {
    const as = [ModInt!MO(3), ModInt!MO(4), ModInt!MO(6), ModInt!MO(10)];
    const cs = as.findLinearRecurrence;
    assert([1, -3, 2] == cs.pretty);
  }
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
