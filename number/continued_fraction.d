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

// Continued fraction of sqrt(D).
//   period: ks[1 .. $]
long[] continuedFractionSqrt(long D) {
  assert(D >= 0);
  const sqrtD = floorSqrt(D);
  long[] ks = [sqrtD];
  // (sqrt(D) + a) / b, b | D - a^2
  const a1 = sqrtD, b1 = D - sqrtD^^2;
  if (!b1) return ks;
  for (long a = a1, b = b1; ; ) {
    const k = (sqrtD + a) / b;
    assert(0 <= a); assert(a <= sqrtD);
    assert(1 <= b); assert(b <= sqrtD + a);
    assert(1 <= k); assert(k <= 2 * sqrtD);
    ks ~= k;
    a = k * b - a;
    b = (D - a^^2) / b;
    if (a == a1 && b == b1) break;
  }
  return ks;
}  // continuedFractionSqrt

unittest {
  assert(continuedFractionSqrt(0) == [0]);
  assert(continuedFractionSqrt(1) == [1]);
  assert(continuedFractionSqrt(2) == [1, 2]);
  assert(continuedFractionSqrt(3) == [1, 1, 2]);
  assert(continuedFractionSqrt(4) == [2]);
  assert(continuedFractionSqrt(5) == [2, 4]);
  assert(continuedFractionSqrt(6) == [2, 2, 4]);
  assert(continuedFractionSqrt(7) == [2, 1, 1, 1, 4]);
  assert(continuedFractionSqrt(8) == [2, 1, 4]);
  assert(continuedFractionSqrt(9) == [3]);
  assert(continuedFractionSqrt(10) == [3, 6]);
  assert(continuedFractionSqrt(11) == [3, 3, 6]);
  assert(continuedFractionSqrt(12) == [3, 2, 6]);
  assert(continuedFractionSqrt(13) == [3, 1, 1, 1, 1, 6]);
  assert(continuedFractionSqrt(14) == [3, 1, 2, 1, 6]);
  assert(continuedFractionSqrt(15) == [3, 1, 6]);

  import std.stdio : writefln;
  foreach (e; 1 .. 6 + 1) {
    size_t maxLen;
    foreach (D; 1 .. 10^^e + 1) {
      const ks = continuedFractionSqrt(D);
      if (maxLen < ks.length) maxLen = ks.length;
    }
    writefln("D <= 10^%s: max |ks| = %s", e, maxLen);
  }
}
/*
D <= 10^1: max |ks| = 5
D <= 10^2: max |ks| = 17
D <= 10^3: max |ks| = 61
D <= 10^4: max |ks| = 218
D <= 10^5: max |ks| = 751
D <= 10^6: max |ks| = 2665
*/

void main() {
}
