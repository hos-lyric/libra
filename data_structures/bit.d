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
  T ret = 0;
  for (int x = pos - 1; x >= 0; x = (x & (x + 1)) - 1) {
    ret += bit[x];
  }
  return ret;
}


bool chmax(T)(ref T t, in T f) { if (t < f) { t = f; return true; } else { return false; } }

void bChmax(T)(T[] bit, int pos, T val)
in {
  assert(0 <= pos && pos < bit.length, "bChmax: 0 <= pos < |bit| must hold");
}
do {
  for (int x = pos; x < bit.length; x |= x + 1) {
    chmax(bit[x], val);
  }
}

// max of [0, pos)
T bMax(T)(T[] bit, int pos)
in {
  assert(0 <= pos && pos <= bit.length, "bMax: 0 <= pos <= |bit| must hold");
}
do {
  T ret = 0;
  for (int x = pos - 1; x >= 0; x = (x & (x + 1)) - 1) {
    chmax(ret, bit[x]);
  }
  return ret;
}


// min pos s.t. pred(sum of [0, pos))
//   assume pred(sum of [0, pos)) is non-decreasing
int bBinarySearch(alias pred, T)(T[] bit) {
  import core.bitop : bsr;
  import std.functional : unaryFun;
  alias predFun = unaryFun!pred;
  if (predFun(0)) return 0;
  int pos = 0;
  T sum = 0;
  foreach_reverse (e; 0 .. bsr(bit.length) + 1) {
    const x = (pos | 1 << e) - 1;
    if (x < bit.length && !predFun(sum + bit[x])) {
      pos |= 1 << e;
      sum += bit[x];
    }
  }
  return pos + 1;
}


unittest {
  {
    auto bit = new long[5];
    bit.bAdd(0, 3);
    bit.bAdd(2, 1);
    bit.bAdd(4, 4);
    assert(bit.bSum(3) == 4);
    bit.bAdd(1, 1);
    bit.bAdd(3, 5);
    assert(bit.bSum(3) == 5);
    assert(bit.bBinarySearch!"a * a > 20" == 3);
  }
  foreach (n; 0 .. 16 + 1) {
    auto bit = new long[n];
    foreach (i; 0 .. n) {
      bit.bAdd(i, 10L^^i);
    }
    foreach (i; 0 .. n + 1) {
      assert(bit.bSum(i) == (10L^^i - 1) / 9);
    }
    assert(bit.bBinarySearch!"a >= 0" == 0);
    assert(bit.bBinarySearch!"a < 0" == n + 1);
    foreach (i; 0 .. n + 1) {
      const sum = (10L^^i - 1) / 9;
      assert(bit.bBinarySearch!(a => (a >= sum)) == i);
      assert(bit.bBinarySearch!(a => (a > sum)) == i + 1);
    }
  }
  {
    auto bit = new long[5];
    bit.bChmax(0, 3);
    bit.bChmax(2, 1);
    bit.bChmax(4, 4);
    assert(bit.bMax(1) == 3);
    assert(bit.bMax(2) == 3);
    assert(bit.bMax(3) == 3);
    assert(bit.bMax(4) == 3);
    assert(bit.bMax(5) == 4);
    bit.bChmax(1, 1);
    bit.bChmax(3, 5);
    assert(bit.bMax(1) == 3);
    assert(bit.bMax(2) == 3);
    assert(bit.bMax(3) == 3);
    assert(bit.bMax(4) == 5);
    assert(bit.bMax(5) == 5);
  }
}

void main() {
}
