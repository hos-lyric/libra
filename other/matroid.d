// Manages linearly independent set in \F_2^n of max weight.
//   S  should be an integral type and support taking a bit and addition (^).
//   T  should support addition and comparison.
//   invariant:  ss[i] = 0  ||  2^i <= ss[i] < 2^(i+1)
class Basis(S, T) {
  import std.algorithm.mutation : swap;
  int n;
  S[] ss;
  T[] ts;
  T total;
  this(int n_) {
    n = n_;
    ss = new S[n];
    ts = new T[n];
    total = 0;
  }
  void add(S s, T t) {
    total += t;
    foreach_reverse (i; 0 .. n) if (s >> i & 1) {
      if (ss[i]) {
        if (ts[i] < t) {
          swap(ss[i], s);
          swap(ts[i], t);
        }
        s ^= ss[i];
      } else {
        ss[i] = s;
        ts[i] = t;
        return;
      }
    }
    total -= t;
  }
}

////////////////////////////////////////////////////////////////////////////////

unittest {
  {
    auto basis = new Basis!(int, long)(3);
    assert(basis.ss == [0, 0, 0]);
    assert(basis.ts == [0, 0, 0]);
    assert(basis.total == 0);
    basis.add(0b011, 10L^^8);
    assert(basis.ss == [0, 0b011, 0]);
    assert(basis.ts == [0, 10L^^8, 0]);
    assert(basis.total == 10L^^8);
    basis.add(0b000, 10L^^10);
    assert(basis.ss == [0, 0b011, 0]);
    assert(basis.ts == [0, 10L^^8, 0]);
    assert(basis.total == 10L^^8);
    basis.add(0b001, 10L^^6);
    assert(basis.ss == [0b001, 0b011, 0]);
    assert(basis.ts == [10L^^6, 10L^^8, 0]);
    assert(basis.total == 10L^^6 + 10L^^8);
    basis.add(0b010, 10L^^12);
    assert(basis.ss == [0b001, 0b010, 0]);
    assert(basis.ts == [10L^^8, 10L^^12, 0]);
    assert(basis.total == 10L^^8 + 10L^^12);
    basis.add(0b110, 10L^^4);
    assert(basis.ss == [0b001, 0b010, 0b110]);
    assert(basis.ts == [10L^^8, 10L^^12, 10L^^4]);
    assert(basis.total == 10L^^8 + 10L^^12 + 10L^^4);
    basis.add(0b100, 10L^^2);
    assert(basis.ss == [0b001, 0b010, 0b110]);
    assert(basis.ts == [10L^^8, 10L^^12, 10L^^4]);
    assert(basis.total == 10L^^8 + 10L^^12 + 10L^^4);
    basis.add(0b101, 10L^^16);
    assert(basis.ss == [0b001, 0b010, 0b101]);
    assert(basis.ts == [10L^^8, 10L^^12, 10L^^16]);
    assert(basis.total == 10L^^8 + 10L^^12 + 10L^^16);
    basis.add(0b111, 10L^^14);
    assert(basis.ss == [0b001, 0b010, 0b101]);
    assert(basis.ts == [10L^^8, 10L^^14, 10L^^16]);
    assert(basis.total == 10L^^8 + 10L^^14 + 10L^^16);
  }
}

void main() {
}
