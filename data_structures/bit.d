void bAdd(T)(T[] bit, int pos, T val)
in {
  assert(0 <= pos && pos < bit.length, "bAdd: 0 <= pos < |bit| must hold");
}
do {
  for (int x = pos; x < bit.length; x |= x + 1) {
    bit[x] += val;
  }
}

// sum of [0, pos)
T bSum(T)(T[] bit, int pos)
in {
  assert(0 <= pos && pos <= bit.length, "bSum: 0 <= pos <= |bit| must hold");
}
do {
  T sum = 0;
  for (int x = pos - 1; x >= 0; x = (x & (x + 1)) - 1) {
    sum += bit[x];
  }
  return sum;
}

// min pos s.t. pred(sum of [0, pos))
int bBinarySearch(alias pred, T)(T[] bit)
in {
  assert(!(bit.length & (bit.length - 1)),
         "bBinarySearch: |bit| must be a power of 2");
}
do {
  import std.functional : unaryFun;
  alias predFun = unaryFun!pred;
  if (predFun(0)) return 0;
  if (!predFun(bit[$ - 1])) return cast(int)(bit.length) + 1;
  int lo = 0, hi = cast(int)(bit.length);
  T sum = 0;
  for (; lo + 1 < hi; ) {
    const mid = (lo + hi) >> 1;
    if (predFun(sum + bit[mid - 1])) {
      hi = mid;
    } else {
      lo = mid;
      sum += bit[mid - 1];
    }
  }
  return hi;
}

unittest {
  auto bit = new long[8];
  foreach (i; 0 .. 8) {
    bit.bAdd(i, 10^^i);
  }
  foreach (i; 0 .. 8 + 1) {
    assert(bit.bSum(i) == (10^^i - 1) / 9);
  }
  assert(bit.bBinarySearch!"a >= 0" == 0);
  assert(bit.bBinarySearch!"a < 0" == 9);
  const x = 11111;
  assert(bit.bBinarySearch!(a => (a >= x)) == 5);
  assert(bit.bBinarySearch!(a => (a > x)) == 6);
}

void main() {
}
