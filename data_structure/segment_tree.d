// TODO: Fix!

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

  // prod of [a, b) (0 <= a <= b <= n)
  T rangeProd(int a, int b) const {
    T prodL = ide, prodR = ide;
    for (a += n, b += n; a < b; a >>= 1, b >>= 1) {
      if (a & 1) prodL = opFun(prodL, ts[a++]);
      if (b & 1) prodR = opFun(ts[--b], prodR);
    }
    return opFun(prodL, prodR);
  }

  // min b s.t. pred(prod of [a, b)) (or n + 1 if no such b)
  //   0 <= a <= n
  //   assume pred(prod of [a, b)) is non-decreasing in b
  int binarySearchR(int a, bool delegate(T) pred) const {
    if (pred(ide)) return a;
    if (a == n) return n + 1;
    T prod = ide;
    for (a += n; ; a >>= 1) {
      if (a & 1) {
        if (pred(opFun(prod, ts[a]))) {
          for (; a < n; ) {
            a <<= 1;
            if (!pred(opFun(prod, ts[a]))) {
              prod = opFun(prod, ts[a++]);
            }
          }
          return a - n + 1;
        }
        prod = opFun(prod, ts[a++]);
        if (!(a & a - 1)) return n + 1;
      }
    }
  }

  // max a s.t. pred(prod of [a, b)) (or -1 if no such a)
  //   0 <= b <= n
  //   assume pred(prod of [a, b)) is non-increasing in a
  int binarySearchL(int b, bool delegate(T) pred) const {
    if (pred(ide)) return b;
    if (b == 0) return -1;
    T prod = ide;
    for (b += n; ; b >>= 1) {
      if ((b & 1) || b == 2) {
        if (pred(opFun(prod, ts[b - 1]))) {
          for (; b <= n; ) {
            b <<= 1;
            if (!pred(opFun(prod, ts[b - 1]))) {
              prod = opFun(prod, ts[--b]);
            }
          }
          return b - n - 1;
        }
        prod = opFun(prod, ts[--b]);
        if (!(b & b - 1)) return -1;
      }
    }
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

// binarySearch
unittest {
  import std.algorithm : max, min;
  enum n = 1 << 4;
  auto seg = new SegmentTree!(int, "a + b", 0)(n, new int[n]);
  foreach (i; 0 .. n) {
    seg.mulR(i, 1);
  }
  foreach (i; 0 .. n + 1) {
    foreach (d; 0 .. n + 2) {
      assert(seg.binarySearchR(i, s => (s >= d)) == min(i + d, n + 1));
      assert(seg.binarySearchL(i, s => (s >= d)) == max(i - d, -1));
    }
  }
}

void main() {
}
