#include "assert.h"
#include <utility>
#include <vector>

using std::swap;
using std::vector;

// TODO: speed up

////////////////////////////////////////////////////////////////////////////////
// Removal costs O(n / (n - (number of elements))) amortized time.
struct UnionFind {
  int n;
  vector<int> uf;
  vector<int> del;
  int pos;
  vector<int> pool;

  UnionFind() {}
  explicit UnionFind(int n_) : n(n_), uf(n, -1), del(n, 0), pos(0), pool(n) {
    for (int u = 0; u < n; ++u) pool[u] = u;
  }
  void rebuild() {
    vector<int> rs(n, -1), tr(n, -1);
    for (int u = 0; u < n; ++u) if (!del[u]) {
      rs[u] = root(u);
      if (!~tr[rs[u]]) tr[rs[u]] = u;
    }
    for (int u = 0; u < n; ++u) if (!del[u]) {
      const int r = tr[rs[u]];
      if (r == u) {
        uf[r] = -1;
      } else {
        --uf[r];
        uf[u] = r;
      }
    }
    pos = 0;
    pool.clear();
    for (int u = 0; u < n; ++u) if (del[u]) {
      uf[u] = -1;
      del[u] = 0;
      pool.push_back(u);
    }
  }
  int add() {
    if (pos >= static_cast<int>(pool.size())) rebuild();
    return pool[pos++];
  }
  void remove(int u) {
    del[u] = 1;
  }
  void cut(int &u) {
    remove(u);
    u = add();
  }
  int root(int u) {
    return (uf[u] < 0) ? u : (uf[u] = root(uf[u]));
  }
  bool connect(int u, int v) {
    u = root(u);
    v = root(v);
    if (u == v) return false;
    if (uf[u] > uf[v]) swap(u, v);
    uf[u] += uf[v];
    uf[v] = u;
    return true;
  }
};

// 0 <= rot < 2^height
// 0 <= depth <= height
// 2^depth <= u < 2^(depth+1)
inline int shiftTreeParent(int height, int rot, int depth, int u) {
  const int two = 1 << depth;
  return (two + ((u + (rot >> (height - depth) & 1)) & (two - 1))) >> 1;
}
inline void shiftTreeChildren(int height, int rot, int depth, int u, int &uL, int &uR) {
  const int two1 = 1 << (depth + 1);
  uR = (u << 1 | 1) - (rot >> (height - (depth + 1)) & 1);
  uL = two1 + ((uR - 1) & (two1 - 1));
}

// l := ceil(log_2(m))
// Maintain sets S and (S \cup (S + (2^(l+1)-m))) to find (S + x) \ S.
struct ModSubsetSum {
  int l, m;
  vector<int> freq;
  vector<int> prv;

  explicit ModSubsetSum(int m_) : m(m_) {
    assert(m >= 1);
    for (l = 0; 1 << l < m; ++l) {}
    freq.assign(m, 0);
  }
  void add(int x) {
    assert(0 <= x); assert(x < m);
    ++freq[x];
  }

  // seg0: S
  // seg1: ((S \cup (S + (2^(l+1)-m))) + r) mod 2^(l+1)
  int r;
  UnionFind uf;
  vector<int> seg0, seg1;
  void init() {
    r = 0;
    uf = UnionFind(1 << (l + 3));  // >= 2^l + 2^(l+1), time vs space
    uf.add();  // 0
    uf.add();  // 1
    seg0.assign(1 << (l + 1), 0);
    seg0[1 << l] = 1;
    for (int u = 1 << l; --u; ) seg0[u] = uf.add();
    seg1.assign(1 << (l + 2), 0);
    seg1[1 << (l + 1)] = seg1[(1 << (l + 2)) - m] = 1;
    for (int u = 1 << (l + 1); --u; ) seg1[u] = uf.add();
    
  }
  void insert0(int x) {
    int u = (1 << l) + x;
    seg0[u] = 1;
    for (; u >>= 1; ) uf.cut(seg0[u]);
  }
  void insert1(int x) {
    int u = (1 << (l + 1)) + x;
    seg1[u] = 1;
    for (int d = l + 1; d > 0; --d) {
      u = shiftTreeParent(l + 1, r, d, u);
      uf.cut(seg1[u]);
    }
  }
  void shiftTo(int rr) {
    if (r != rr) {
      const int d = l + 1 - __builtin_ctz(rr - r);
      r = rr;
      for (int u = 1 << d; --u; ) uf.cut(seg1[u]);
    }
  }
  vector<int> diff;
  bool getDiff(int d, int u0, int u1, int b) {
    if (uf.root(seg0[u0]) == uf.root(seg1[u1])) return false;
    if (d == l) {
      if (seg0[u0] == 0 && seg1[u1] == 1) diff.push_back(u0 - (1 << l));
      return (seg0[u0] != seg1[u1]);
    }
    int u1L, u1R;
    shiftTreeChildren(l + 1, r, d + 1, u1, u1L, u1R);
    
    const int mid = 1 << (l - (d + 1));
    if (b <= mid) {
      return getDiff(d + 1, u0 << 1, u1L, b);
    } else {
      const bool resL = getDiff(d + 1, u0 << 1, u1L, mid);
      const bool resR = getDiff(d + 1, u0 << 1 | 1, u1R, b - mid);
      if (resL || resR) {
        return true;
      } else {
        if (b == 1 << (l - d)) {
          uf.connect(seg0[u0], seg1[u1]);
        }
        return false;
      }
    }
  }

  // Modify freq so that freq[x] <= 2.
  // It is no longer possible to recover the solution for the original freq.
  void reduce() {
    for (int x = 0; x < m; ++x) {
      for (int y = x; freq[y] >= 3; ) {
        int yy = 2 * y;
        yy = (yy >= m) ? (yy - m) : yy;
        const int t = (freq[y] - 1) / 2;
        freq[y] -= 2 * t;
        freq[yy] += t;
        y = yy;
      }
    }
  }
  // O((\sum_x freq[x] + m) (log m) \alpha(m))
  void run() {
    init();
    prv.assign(m, -1);
    prv[0] = -2;
    for (int i = 1, x = 0; i < 1 << l; ++i) {
      x ^= 1 << (l - 1 - __builtin_ctz(i));
      if (x < m && freq[x] > 0) {
        shiftTo(x);
        for (int j = 0; j < freq[x]; ++j) {
          diff.clear();
          getDiff(0, 1, 2, m);
          for (const int s : diff) if (s < m) {
            prv[s] = x;
            insert0(s);
            insert1(s);
            insert1((1 << (l + 1)) - m + s);
          }
        }
      }
    }
  }
  bool operator[](int s) const {
    assert(0 <= s); assert(s < m);
    return (~prv[s]);
  }
  vector<int> recover(int s) const {
    assert(0 <= s); assert(s < m);
    assert(~prv[s]);
    vector<int> sol(m, 0);
    for (; s != 0; ) {
      const int x = prv[s];
      ++sol[x];
      s -= x;
      s = (s < 0) ? (s + m) : s;
    }
    return sol;
  }
};
////////////////////////////////////////////////////////////////////////////////

#include <bitset>

using std::bitset;

void unittest() {
  // UnionFind
  {
    constexpr int n = 8;
    UnionFind uf(n);
    for (int u = 0; u < n; ++u) {
      assert(uf.add() == u);
    }
    uf.connect(0, 2);
    uf.connect(0, 4);
    uf.connect(3, 5);
    uf.connect(5, 7);
    uf.remove(0);
    {
      int u = 5;
      uf.cut(u);
      assert(u == 0);
    }
    assert(uf.add() == 5);
    constexpr int ids[n] = {0, 1, 2, 3, 2, 5, 6, 3};
    for (int u = 0; u < n; ++u) for (int v = 0; v < n; ++v) {
      assert((uf.root(u) == uf.root(v)) == (ids[u] == ids[v]));
    }
  }
  // shift tree
  {
    //  1                                             
    //  3                       2                     
    //  6           7           4           5         
    // 11    12    13    14    15     8     9    10   
    // 21 22 23 24 25 26 27 28 29 30 31 16 17 18 19 20
    constexpr int height = 4;
    constexpr int rot = 11;
    constexpr int par[1 << (height + 1)] = {
      0,
      0,
      1, 1,
      2, 2, 3, 3,
      4, 5, 5, 6, 6, 7, 7, 4,
      8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 15, 8,
    };
    constexpr int lef[1 << height] = {
      0,
      3,
      4, 6,
      15, 9, 11, 13,
      31, 17, 19, 21, 23, 25, 27, 29,
    };
    constexpr int rig[1 << height] = {
      0,
      2,
      5, 7,
      8, 10, 12, 14,
      16, 18, 20, 22, 24, 26, 28, 30,
    };
    for (int depth = 0; depth <= height; ++depth) {
      for (int u = 1 << depth; u < 1 << (depth + 1); ++u) {
        if (depth > 0) {
          assert(shiftTreeParent(height, rot, depth, u) == par[u]);
        }
        if (depth < height) {
          int uL = 0, uR = 0;
          shiftTreeChildren(height, rot, depth, u, uL, uR);
          assert(uL == lef[u]);
          assert(uR == rig[u]);
        }
      }
    }
  }
  // ModSubsetSum
  {
    ModSubsetSum mss(12);
    mss.add(10);
    mss.add(10);
    mss.add(7);
    mss.add(10);
    mss.add(10);
    mss.reduce();
    assert(mss.freq == (vector<int>{0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0}));
    mss.run();
    for (int i = 0; i <= 1; ++i) for (int j = 0; j <= 4; ++j) {
      assert(mss[(i * 7 + j * 10) % 12]);
    }
    assert(!mss[2]);
    assert(!mss[9]);
  }
  {
    ModSubsetSum mss(8);
    mss.add(5);
    mss.add(3);
    mss.run();
    assert(mss[0]);
    assert(!mss[1]);
    assert(!mss[2]);
    assert(mss[3]);
    assert(!mss[4]);
    assert(mss[5]);
    assert(!mss[6]);
    assert(!mss[7]);
  }
  {
    ModSubsetSum mss(7);
    mss.add(5);
    mss.add(4);
    mss.add(5);
    mss.add(2);
    mss.add(1);
    mss.run();
    assert(mss[0]);
    assert(mss[1]);
    assert(mss[2]);
    assert(mss[3]);
    assert(mss[4]);
    assert(mss[5]);
    assert(mss[6]);
  }
  {
    ModSubsetSum mss(8);
    mss.add(6);
    mss.add(6);
    mss.add(2);
    mss.run();
    assert(mss[0]);
    assert(!mss[1]);
    assert(mss[2]);
    assert(!mss[3]);
    assert(mss[4]);
    assert(!mss[5]);
    assert(mss[6]);
    assert(!mss[7]);
  }
  {
    constexpr int lim = 12;
    vector<int> three(lim + 1);
    three[0] = 1;
    for (int i = 1; i <= lim; ++i) three[i] = three[i - 1] * 3;
    for (int m = 1; m <= lim; ++m) {
      for (int p = 0; p < three[m]; ++p) {
        vector<int> freq(m, 0);
        int pp = p;
        for (int x = 0; x < m; ++x) {
          freq[x] = pp % 3;
          pp /= 3;
        }
        bitset<(lim << 1)> bs;
        bs.set(0);
        for (int x = 0; x < m; ++x) for (int j = 0; j < freq[x]; ++j) {
          bs |= bs << x | bs >> (m - x);
        }
        ModSubsetSum mss(m);
        for (int x = 0; x < m; ++x) for (int j = 0; j < freq[x]; ++j) {
          mss.add(x);
        }
        mss.run();
        for (int s = 0; s < m; ++s) {
          assert(bs[s] == mss[s]);
        }
        for (int s = 0; s < m; ++s) if (mss[s]) {
          const vector<int> sol = mss.recover(s);
          int sum = 0;
          for (int x = 0; x < m; ++x) {
            assert(0 <= sol[x]); assert(sol[x] <= freq[x]);
            sum += sol[x] * x;
          }
          sum %= m;
          assert(sum == s);
        }
      }
    }
  }
}

int main() {
  unittest();
  return 0;
}
