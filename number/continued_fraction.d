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

// Continued fraction of sqrt(d)
//   period: ks[1 .. $]
long[] continuedFractionSqrt(long d) {
  const sqrtD = floorSqrt(d);
  assert(d != sqrtD^^2);
  long[] ks = [sqrtD];
  // (sqrt(d) + a) / b, b | d - a^2
  const a1 = sqrtD, b1 = d - sqrtD^^2;
  for (long a = a1, b = b1; ; ) {
    const k = (sqrtD + a) / b;
    assert(0 <= a && a <= 2 * sqrtD);
    assert(1 <= b && b <= 2 * sqrtD);
    assert(1 <= k && k <= 2 * sqrtD);
    ks ~= k;
    a = k * b - a;
    b = (d - a^^2) / b;
    if (a == a1 && b == b1) break;
  }
  return ks;
}

unittest {
  assert(continuedFractionSqrt(2) == [1, 2]);
  assert(continuedFractionSqrt(3) == [1, 1, 2]);
  assert(continuedFractionSqrt(5) == [2, 4]);
  assert(continuedFractionSqrt(6) == [2, 2, 4]);
  assert(continuedFractionSqrt(7) == [2, 1, 1, 1, 4]);
  assert(continuedFractionSqrt(8) == [2, 1, 4]);
  assert(continuedFractionSqrt(10) == [3, 6]);
  assert(continuedFractionSqrt(11) == [3, 3, 6]);
  assert(continuedFractionSqrt(12) == [3, 2, 6]);
  assert(continuedFractionSqrt(13) == [3, 1, 1, 1, 1, 6]);
  assert(continuedFractionSqrt(14) == [3, 1, 2, 1, 6]);
  assert(continuedFractionSqrt(15) == [3, 1, 6]);
}

void main() {
}
