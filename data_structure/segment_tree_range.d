// T, S: monoid
// opTT: T * T -> T
// opST: S * T * int -> T
//   (s t_a) ... (s t_{b-1}) = opST(s, t_a ... t_{b-1}, b - a)
// opSS: S * S -> S
// query(a, b, s): t_a <- s t_a, ..., t_{b-1} <- s t_{b-1};
//   returns t_a ... t_{b-1}
class SegmentTree(T, S, alias opTT, alias opST, alias opSS, T idT_, S idS_) {
  import std.functional : binaryFun;
  alias opTTFun = binaryFun!opTT;
  alias opSTFun = opST;
  alias opSSFun = binaryFun!opSS;
  alias idT = idT_;
  alias idS = idS_;

  int n;
  T[] ts;
  S[] ss;
  this(int n_) {
    for (n = 1; n < n_; n <<= 1) {}
    ts = new T[n << 1];
    ss = new S[n << 1];
    ts[] = idT;
    ss[] = idS;
  }
  ref T at(int a) {
    return ts[n + a];
  }
  void build() {
    foreach_reverse (a; 1 .. n) ts[a] = opTTFun(ts[a << 1], ts[a << 1 | 1]);
  }
  T query(int a, int b, const(S) s) {
    return query(1, 0, n, a, b, s);
  }

 private:
  T query(int u, int l, int r, int a, int b, const(S) s) {
    if (a < l) a = l;
    if (b > r) b = r;
    if (a >= b) return idT;
    if (a == l && b == r) {
      ts[u] = opSTFun(s, ts[u], r - l);
      ss[u] = opSSFun(s, ss[u]);
      return ts[u];
    }
    const int uL = u << 1, uR = u << 1 | 1;
    const int mid = (l + r) >> 1;
    // speed-up: if (ss[u] != idS)
    {
      ts[uL] = opSTFun(ss[u], ts[uL], mid - l);
      ts[uR] = opSTFun(ss[u], ts[uR], r - mid);
      ss[uL] = opSSFun(ss[u], ss[uL]);
      ss[uR] = opSSFun(ss[u], ss[uR]);
      ss[u] = idS;
    }
    const T resL = query(uL, l, mid, a, b, s);
    const T resR = query(uR, mid, r, a, b, s);
    ts[u] = opTTFun(ts[uL], ts[uR]);
    return opTTFun(resL, resR);
  }
}

unittest {
  auto xs = new int[10];
  auto seg = new SegmentTree!(int, int, "a + b", (s, t, sz) => t + s * sz,
                              "a + b", 0, 0)(10);
  void rangeAdd(int a, int b, int s) {
    int expected;
    foreach (i; a .. b) {
      xs[i] += s;
      expected += xs[i];
    }
    const received = seg.query(a, b, s);
    assert(expected == received);
  }
  rangeAdd(3, 1, 4);
  rangeAdd(1, 5, 9);
  rangeAdd(2, 6, 5);
  rangeAdd(3, 5, 8);
  rangeAdd(9, 7, 9);
  rangeAdd(0, 10, 100);
  rangeAdd(0, 10, 100);
  rangeAdd(3, 2, 3);
  rangeAdd(8, 4, 6);
  rangeAdd(2, 6, 4);
  rangeAdd(3, 3, 8);
  rangeAdd(3, 2, 7);
}

void main() {
}
