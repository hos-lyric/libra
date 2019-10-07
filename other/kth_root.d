// floor(a^(1/k))
ulong floorKthRoot(ulong a, ulong k) {
  import core.bitop : bsr;
  import std.algorithm : min;
  if (a == 0) {
    return 0;
  } else if (k <= 1) {
    return a;
  } else if (k == 2) {
    ulong b = a, x = 0, y = 0;
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
  } else if (k <= 40) {
    // min x s.t. x^k >= 2^64
    enum ulong[] HIS =
        [0, 0, 4294967296UL, 2642246, 65536, 7132, 1626, 566, 256, 139, 85, 57,
         41, 31, 24, 20, 16, 14, 12, 11, 10, 9, 8, 7, 7, 6, 6, 6, 5, 5, 5, 5,
         4, 4, 4, 4, 4, 4, 4, 4, 4];
    ulong lo = 1UL << (bsr(a) / k);
    ulong hi = min(1UL << (bsr(a) / k + 1), HIS[cast(size_t)(k)]);
    for (; lo + 1 < hi; ) {
      const ulong mid = (lo + hi) / 2;
      ulong b = mid * mid;
      foreach (i; 2 .. k) b *= mid;
      ((b <= a) ? lo : hi) = mid;
    }
    return lo;
  } else if (k <= 63) {
    return ((1UL << k) <= a) ? 2 : 1;
  } else {
    return 1;
  }
}

unittest {
  // k = 2
  for (ulong x = 0; x < 1000; ++x) {
    for (ulong a = x * x; a < (x + 1) * (x + 1); ++a) {
      assert(floorKthRoot(a, 2) == x);
    }
  }
  for (ulong x = 4294967295UL - 1000; x <= 4294967295UL; ++x) {
    for (ulong a = x * x - 1000; a < x * x; ++a) {
      assert(floorKthRoot(a, 2) == x - 1);
    }
    for (ulong a = x * x; a < x * x + 1000; ++a) {
      assert(floorKthRoot(a, 2) == x);
    }
  }
  for (ulong b = 1; b <= 1000; ++b) {
    assert(floorKthRoot(-b, 2) == 4294967295UL);
  }

  // general
  for (ulong x = 2; x < 1000; ++x) {
    ulong a = x;
    for (int k = 1; ; ++k) {
      assert(floorKthRoot(a - 1, k) == x - 1);
      assert(floorKthRoot(a, k) == x);
      if (a > ~0UL / x) break;
      a *= x;
    }
  }
}

void main() {
}
