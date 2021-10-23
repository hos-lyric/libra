#include <utility>
#include <vector>

using std::swap;
using std::vector;

// Manages linearly independent set in \F_2^n of max weight.
//   S  should be an integral type and support taking a bit and addition (^).
//   T  should support addition and comparison.
//   invariant:  ss[i] = 0  ||  2^i <= ss[i] < 2^(i+1)
template <class S, class T> struct Basis {
  int n;
  vector<S> ss;
  vector<T> ts;
  T total;
  Basis(int n_) : n(n_), ss(n, 0), ts(n, 0), total(0) {}
  void add(S s, T t) {
    total += t;
    for (int i = n; --i >= 0; ) if (s >> i & 1) {
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
};

////////////////////////////////////////////////////////////////////////////////

#include <assert.h>

void unittest() {
  {
    Basis<int, long long> basis(3);
    assert(basis.ss == (vector<int>{0, 0, 0}));
    assert(basis.ts == (vector<long long>{0, 0, 0}));
    assert(basis.total == 0);
    basis.add(0b011, 8);
    assert(basis.ss == (vector<int>{0, 0b011, 0}));
    assert(basis.ts == (vector<long long>{0, 8, 0}));
    assert(basis.total == 8);
    basis.add(0b000, 10);
    assert(basis.ss == (vector<int>{0, 0b011, 0}));
    assert(basis.ts == (vector<long long>{0, 8, 0}));
    assert(basis.total == 8);
    basis.add(0b001, 6);
    assert(basis.ss == (vector<int>{0b001, 0b011, 0}));
    assert(basis.ts == (vector<long long>{6, 8, 0}));
    assert(basis.total == 6 + 8);
    basis.add(0b010, 12);
    assert(basis.ss == (vector<int>{0b001, 0b010, 0}));
    assert(basis.ts == (vector<long long>{8, 12, 0}));
    assert(basis.total == 8 + 12);
    basis.add(0b110, 4);
    assert(basis.ss == (vector<int>{0b001, 0b010, 0b110}));
    assert(basis.ts == (vector<long long>{8, 12, 4}));
    assert(basis.total == 8 + 12 + 4);
    basis.add(0b100, 2);
    assert(basis.ss == (vector<int>{0b001, 0b010, 0b110}));
    assert(basis.ts == (vector<long long>{8, 12, 4}));
    assert(basis.total == 8 + 12 + 4);
    basis.add(0b101, 16);
    assert(basis.ss == (vector<int>{0b001, 0b010, 0b101}));
    assert(basis.ts == (vector<long long>{8, 12, 16}));
    assert(basis.total == 8 + 12 + 16);
    basis.add(0b111, 14);
    assert(basis.ss == (vector<int>{0b001, 0b010, 0b101}));
    assert(basis.ts == (vector<long long>{8, 14, 16}));
    assert(basis.total == 8 + 14 + 16);
  }
}

int main() {
  unittest();
  return 0;
}
