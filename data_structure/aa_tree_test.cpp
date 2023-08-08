#include "aa_tree.h"

#include <assert.h>
#include <algorithm>
#include <iostream>
#include <vector>

using std::cerr;
using std::endl;
using std::swap;
using std::vector;

////////////////////////////////////////////////////////////////////////////////
// !!!Size must be a signed integer type!!!
// range add, range sum
template <class Size_, class T> struct NodeSum {
  using Size = Size_;
  Size sz;
  T sum, lz;
  NodeSum() : sz(0), sum(0), lz(0) {}
  void init(Size sz_) {
    sz = sz_;
  }
  void push(NodeSum &l, NodeSum &r) {
    if (lz) {
      l.add(lz);
      r.add(lz);
      lz = 0;
    }
  }
  void pull(const NodeSum &l, const NodeSum &r) {
    sz = l.sz + r.sz;
    sum = l.sum + r.sum;
  }
  void add(const T &val) {
    sum += static_cast<T>(sz) * val;
    lz += val;
  }
  T getSum() const {
    return sum;
  }
};
////////////////////////////////////////////////////////////////////////////////

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

void unittest() {
  constexpr int NUM_CASES = 1000;
  constexpr int MAX_N = 100;
  constexpr int NUM_QUERIES = 1000;
  for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
    const int n = 1 + xrand() % MAX_N;
    vector<long long> xs(n + 1, 0);
    for (int i = 1; i <= n; ++i) {
      xs[i] = static_cast<long long>(xrand()) << 20;
      xs[i] |= xrand();
    }
    std::sort(xs.begin(), xs.end());
    vector<int> is{0, n};
    vector<unsigned> brt(n, 0);
    using Node = NodeSum<long long, unsigned>;
    using AA = AATree<Node>;
    AA *seg = new AA(xs[n]);
    for (int q = 0; q < NUM_QUERIES; ++q) {
      switch (xrand() % 3) {
        case 0: {
          const int i = xrand() % (n + 1);
          is.push_back(i);
          std::sort(is.begin(), is.end());
          is.erase(std::unique(is.begin(), is.end()), is.end());
          AA::cut(seg, xs[i]);
        } break;
        case 1: {
          int a = is[xrand() % is.size()];
          int b = is[xrand() % is.size()];
          if (a > b) swap(a, b);
          const unsigned val = xrand();
          for (int i = a; i < b; ++i) {
            brt[i] += val;
          }
          seg->ch(xs[a], xs[b], &Node::add, val);
        } break;
        case 2: {
          int a = is[xrand() % is.size()];
          int b = is[xrand() % is.size()];
          if (a > b) swap(a, b);
          unsigned expected = 0;
          for (int i = a; i < b; ++i) {
            expected += static_cast<unsigned>(xs[i + 1] - xs[i]) * brt[i];
          }
          const unsigned actual0 = seg->get(xs[a], xs[b]).sum;
          const unsigned actual1 = seg->get(
              xs[a], xs[b],
              [&](unsigned x, unsigned y) -> unsigned { return x + y; },
              [&]() -> unsigned { return 0; },
              &Node::getSum);
          assert(expected == actual0);
          assert(expected == actual1);
        } break;
        default: assert(false);
      }
    }
    AA::free(seg);
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
