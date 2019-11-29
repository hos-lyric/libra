import std.typecons : Tuple, tuple;

uint xrand() {
  static uint x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  uint t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

// p = a^2 + b^2
//   p == 1 (mod 4), prime
Tuple!(long, long) serret(long p) {
  long a = p, b;
  for (; ; ) {
    b = 1;
    long c = 2 + xrand() % (p - 2);
    for (long e = (p - 1) / 4; e; e >>= 1) {
      if (e & 1) b = (b * c) % p;
      c = (c * c) % p;
    }
    if ((b * b) % p == p - 1) {
      break;
    }
  }
  for (; ; ) {
    const r = a % b;
    a = b;
    b = r;
    if (a * a < p) {
      return tuple(a, b);
    }
  }
}

unittest {
  assert(serret(5) == tuple(2, 1));
  assert(serret(13) == tuple(3, 2));
  assert(serret(17) == tuple(4, 1));
  assert(serret(29) == tuple(5, 2));
  assert(serret(1_000_000_009) == tuple(31400, 3747));
}

void main() {
}
