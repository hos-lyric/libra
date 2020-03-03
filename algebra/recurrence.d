// dmd -O -unittest recurrence ../number/modint
import modint;

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
