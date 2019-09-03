// point update, range product
//   T: monoid
class SegmentTree(T, alias op, T ide) {
  import std.functional : binaryFun;
  alias opFun = binaryFun!op;
  int n;
  T[] ts;
  this(int n_) {
    for (n = 1; n < n_; n <<= 1) {}
    ts = new T[n << 1];
    ts[] = ide;
  }
  this(int n_, T[] ini) {
    for (n = 1; n < n_; n <<= 1) {}
    ts = new T[n << 1];
    ts[0 .. n] = ide;
    ts[n .. n + n_] = ini[];
    ts[n + n_ .. n << 1] = ide;
    foreach_reverse (a; 1 .. n) ts[a] = opFun(ts[a << 1], ts[a << 1 | 1]);
  }

  // 0 <= a < n
  T get(int a) const {
    return ts[a + n];
  }
  void update(int a, in T val) {
    ts[a += n] = val;
    for (; a >>= 1; ) ts[a] = opFun(ts[a << 1], ts[a << 1 | 1]);
  }
  void mulL(int a, in T val) {
    update(a, opFun(val, ts[a + n]));
  }
  void mulR(int a, in T val) {
    update(a, opFun(ts[a + n], val));
  }

  // [a, b) (0 <= a <= b <= n)
  T rangeProd(int a, int b) const {
    T prodL = ide, prodR = ide;
    for (a += n, b += n; a < b; a >>= 1, b >>= 1) {
      if (a & 1) prodL = opFun(prodL, ts[a++]);
      if (b & 1) prodR = opFun(ts[--b], prodR);
    }
    return opFun(prodL, prodR);
  }
}

unittest {
  enum n = 26;
  auto ini = new string[n];
  foreach (i; 0 .. n) {
    ini[i] = "" ~ cast(char)('a' + i);
  }
  auto seg = new SegmentTree!(string, "a ~ b", "")(n, ini);
  seg.update(15, "P");
  seg.mulL(17, "^");
  seg.mulR(19, "$");
  seg.update(21, "V");
  assert(seg.get(17) == "^r");
  assert(seg.rangeProd(15, 21) == "Pq^rst$u");
}

void main() {
}
