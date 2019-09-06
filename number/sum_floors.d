// floor(a / m)
// m > 0
long floor(long a, long m) {
  return a / m - ((a % m < 0) ? 1 : 0);
}

// sum{ floor((a x + b) / m) | l <= x <= r }
// m > 0
long sumFloors(long m, long a, long b, long l, long r)
in {
  assert(m > 0, "sumFloors: m > 0 must hold");
}
do {
  long sum;
  for (; l <= r; ) {
    const q = floor(a, m);
    const aa = a - q * m;
    const ll = floor(aa * l + b, m) + 1;
    const rr = floor(aa * r + b, m);
    sum += q * ((r + 1) * r / 2 - l * (l - 1) / 2) + r * rr - (l - 1) * (ll - 1) + (rr - ll + 1);
    a = m; m = aa; l = -rr; r = -ll;
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
        sum += floor(a * x + b, m);
      }
      assert(sumFloors(m, a, b, l, r) == sum);
    }
  }
}

void main() {
}
