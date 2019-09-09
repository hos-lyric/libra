long gcd(long a, long b) {
  import core.bitop : bsf;
  import std.algorithm.mutation : swap;
  if (a < 0) a = -a;
  if (b < 0) b = -b;
  if (a == 0) return b;
  if (b == 0) return a;
  const int s = bsf(a | b);
  a >>= bsf(a);
  do {
    b >>= bsf(b);
    if (a > b) swap(a, b);
    b -= a;
  } while (b);
  return a << s;
}

unittest {
  enum LIM = 500;
  foreach (a; -LIM .. LIM) foreach (b; -LIM .. LIM) {
    int g;
    if (a == 0 && b == 0) {
      g = 0;
    } else {
      for (g = LIM; g; --g) {
        if (a % g == 0 && b % g == 0) {
          break;
        }
      }
    }
    assert(gcd(a, b) == g);
  }
}

void main() {
}
