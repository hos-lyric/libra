// floor(n/x) = k
// <=>  k <= n/x < k+1
// <=>  n/(k+1) < x <= n/k
// <=>  floor(n/(k+1)) < x <= floor(n/k)
void doFloors(alias fun, T)(const(T) n) {
  assert(n >= 1);
  for (T a = 0, b; a < n; a = b) {
    const k = n / (a + 1);
    b = n / k;
    // (a, b]: k
    fun(a, b, k);
  }
}

// ceil(n/x) = k
// <=>  k-1 < n/x <= k
// <=>  n/k <= x < n/(k-1)
// <=>  ceil(n/k) <= x < ceil(n/(k-1))
// ceil(n/x) = floor((n-1)/x) + 1
void doCeils(alias fun, T)(const(T) n) {
  assert(n >= 1);
  for (T a = 0, b; a < n - 1; a = b) {
    const k = (n - 1) / (a + 1) + 1;
    b = (n - 1) / (k - 1);
    // (a, b]: k
    fun(a, b, k);
  }
  // n: 1
  fun(n - 1, n, 1);
}

////////////////////////////////////////////////////////////////////////////////

// floor(n/x)
// m := floor(sqrt(n))
//   - k               for  1 <= k <= m
//   - k = floor(n/l)  for  1 <= l <= floor(n/(m+1))  (l = floor(n/k))

// ceil(n/x)
// m := ceil(sqrt(n))
//   - k              for  1 <= k <= m
//   - k = ceil(n/l)  for  1 <= l <= floor((n-1)/m)  (l = ceil(n/k))

////////////////////////////////////////////////////////////////////////////////

unittest {
  enum LIM = 1000;

  foreach (n; 1 .. LIM + 1) {
    auto cnt = new long[n + 1];
    long[] ks;
    void checkFloor(long a, long b, long k) {
      assert(0 <= a);
      assert(a < b);
      assert(b <= n);
      foreach (x; a + 1 .. b + 1) {
        assert(n / x == k);
        ++cnt[x];
      }
      ks ~= k;
    }
    doFloors!checkFloor(n);
    foreach (x; 1 .. n + 1) {
      assert(cnt[x] == 1);
    }

    long m;
    for (; m^^2 <= n; ++m) {}
    --m;
    long[] kks;
    foreach (l; 1 .. n / (m + 1) + 1) {
      const k = n / l;
      assert(l == n / k);
      kks ~= k;
    }
    foreach_reverse (k; 1 .. m + 1) {
      kks ~= k;
    }
    assert(ks == kks);
  }

  foreach (n; 1 .. LIM + 1) {
    auto cnt = new long[n + 1];
    long[] ks;
    void checkCeil(long a, long b, long k) {
      assert(0 <= a);
      assert(a < b);
      assert(b <= n);
      foreach (x; a + 1 .. b + 1) {
        assert((n + x - 1) / x == k);
        ++cnt[x];
      }
      ks ~= k;
    }
    doCeils!checkCeil(n);
    foreach (x; 1 .. n + 1) {
      assert(cnt[x] == 1);
    }

    long m;
    for (; m^^2 < n; ++m) {}
    long[] kks;
    foreach (l; 1 .. (n - 1) / m + 1) {
      const k = (n + l - 1) / l;
      assert(l == (n + k - 1) / k);
      kks ~= k;
    }
    foreach_reverse (k; 1 .. m + 1) {
      kks ~= k;
    }
    assert(ks == kks);
  }
}

void main() {
  import std.algorithm, std.math, std.range, std.stdio;
  foreach (n; 1 .. 25 + 1) {
    const m = cast(int)(floor(sqrt(cast(real)(n))));
    writeln(n, " ", n / (m + 1), " ", iota(1, m + 1), " ", iota(1, m + 1).map!(l => n / l));
  }
  foreach (n; 1 .. 25 + 1) {
    const m = cast(int)(ceil(sqrt(cast(real)(n))));
    writeln(n, " ", (n - 1) / m, " ", iota(1, m + 1), " ", iota(1, m + 1).map!(l => (n + l - 1) / l));
  }
}
