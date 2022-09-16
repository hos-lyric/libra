// floor(a / b)
Int divFloor(Int)(Int a, Int b) {
  return a / b - (((a ^ b) < 0 && a % b != 0) ? 1 : 0);
}

// sum_{x=l}^r floor((a x + b) / m)
// m > 0
long sumFloors(long m, long a, long b, long l, long r)
in {
  assert(m > 0, "sumFloors: m > 0 must hold");
}
do {
  long sum;
  for (; l <= r; ) {
    const q = divFloor(a, m);
    const aa = a - q * m;
    const ll = divFloor(aa * l + b, m) + 1;
    const rr = divFloor(aa * r + b, m);
    // TODO: overflow if ll or rr is big in recursion
    sum += q * ((r + 1) * r / 2 - l * (l - 1) / 2) + r * rr - (l - 1) * (ll - 1) + (rr - ll + 1);
    a = m; m = aa; l = -rr; r = -ll;
  }
  return sum;
}

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

// \sum_{x=1}^n floor(sqrt(d) x)
long sumFloorsSqrt(long d, long n)
in {
  assert(d >= 2, "sumFloorsSqrt: d >= 2 must hold");
  assert(n >= 0, "sumFloorsSqrt: n >= 0 must hold");
}
do {
  const sqrtD = floorSqrt(d);
  assert(d > sqrtD^^2, "sumFloorsSqrt: d must not be a perfect square");
  long sum, sig = 1;
  // (sqrt(d) - a) / b
  long a = 0, b = 1;
  for (; n > 0; ) {
    // TODO: precision
    import std.math : floor, sqrt;
    const k = (sqrtD + a) / b;
    sum += sig * k * (n * (n + 1) / 2);
    const nn = cast(long)(floor((sqrt(cast(real)(d)) + a - k * b) / b * n));
    sum += sig * n * nn;
    a = k * b - a;
    b = (d - a^^2) / b;
    sig *= -1;
    n = nn;
  }
  return sum;
}

unittest {
  // https://judge.yosupo.jp/problem/sum_of_floor_of_linear
  assert(sumFloors(10, 6, 3, 0, 4 - 1) == 3);
  assert(sumFloors(5, 4, 3, 0, 6 - 1) == 13);
  assert(sumFloors(1, 0, 0, 0, 1 - 1) == 0);
  assert(sumFloors(92653, 58979, 32384, 0, 31415 - 1) == 314095480);
  assert(sumFloors(1000000000, 999999999, 999999999, 0, 1000000000 - 1) ==
         499999999500000000L);

  enum long LIM = 10;
  foreach (m; 1 .. LIM) foreach (a; -LIM .. LIM) foreach (b; -LIM .. LIM) {
    foreach (l; -LIM .. LIM) foreach (r; -LIM .. LIM) {
      long sum;
      foreach (x; l .. r + 1) {
        sum += divFloor(a * x + b, m);
      }
      assert(sumFloors(m, a, b, l, r) == sum);
    }
  }
}

unittest {
  assert(sumFloorsSqrt(7, 0) == 0);
  assert(sumFloorsSqrt(7, 10) == 140);
  assert(sumFloorsSqrt(7, 20) == 545);
}

void main() {
}
