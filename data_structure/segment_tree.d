// T: monoid
// op: T * T -> T
// query(a, b): returns t_a ... t_{b-1}
class SegmentTree(T, alias op, T idT_) {
  import std.functional : binaryFun;
  alias opFun = binaryFun!op;
  alias idT = idT_;

  int n;
  T[] ts;
  this(int n_) {
    for (n = 1; n < n_; n <<= 1) {}
    ts = new T[n << 1];
    ts[] = idT;
  }
  this(int n_, inout(T)[] ts_) {
    for (n = 1; n < n_; n <<= 1) {}
    ts = new T[n << 1];
    ts[0 .. n] = idT;
    ts[n .. n + n_] = ts_[];
    ts[n + n_ .. n << 1] = idT;
    build();
  }
  ref T at(int a) {
    return ts[n + a];
  }
  void build() {
    foreach_reverse (a; 1 .. n) ts[a] = opFun(ts[a << 1], ts[a << 1 | 1]);
  }
  void set(int a, const(T) val) {
    ts[a += n] = val;
    for (; a >>= 1; ) ts[a] = opFun(ts[a << 1], ts[a << 1 | 1]);
  }
  void mulL(int a, const(T) val) {
    set(a, opFun(val, ts[a + n]));
  }
  void mulR(int a, const(T) val) {
    set(a, opFun(ts[a + n], val));
  }
  T query(int a, int b) const {
    T prodL = idT, prodR = idT;
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
    if (pred(idT)) return a;
    if (a == n) return n + 1;
    T prod = idT;
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
    if (pred(idT)) return b;
    if (b == 0) return -1;
    T prod = idT;
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
  seg.set(15, "P");
  seg.mulL(17, "^");
  seg.mulR(19, "$");
  seg.set(21, "V");
  assert(seg.at(17) == "^r");
  assert(seg.query(15, 21) == "Pq^rst$u");
}

// binarySearch
unittest {
  import std.algorithm : max, min;
  enum n = 1 << 4;
  const ini = new int[n];
  auto seg = new SegmentTree!(int, "a + b", 0)(n, ini);
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
