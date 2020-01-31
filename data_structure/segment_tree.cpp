#include <assert.h>
#include <stdio.h>
#include <vector>

using std::vector;

template <class T, class S, class OpTT, class OpST, class OpSS>
struct SegmentTree {
  const OpTT opTT;
  const OpST opST;
  const OpSS opSS;
  const T idT;
  const S idS;

  int n;
  vector<T> ts;
  vector<S> ss;
  SegmentTree(int n_, const OpTT opTT, const OpST opST, const OpSS opSS,
              const T &idT, const S &idS)
      : opTT(opTT), opST(opST), opSS(opSS), idT(idT), idS(idS) {
    for (n = 1; n < n_; n <<= 1) {}
    ts.assign(n << 1, idT);
    ss.assign(n << 1, idS);
  }
  T &at(int a) {
    return ts[n + a];
  }
  void build() {
    for (int a = n; --a; ) ts[a] = opTT(ts[a << 1], ts[a << 1 | 1]);
  }
  T query(int a, int b, const S &s) {
    return query(1, 0, n, a, b, s);
  }

 private:
  T query(int u, int l, int r, int a, int b, const S &s) {
    if (a < l) a = l;
    if (b > r) b = r;
    if (a >= b) return idT;
    if (a == l && b == r) {
      ts[u] = opST(s, ts[u], r - l);
      ss[u] = opSS(s, ss[u]);
      return ts[u];
    }
    const int uL = u << 1, uR = u << 1 | 1;
    const int mid = (l + r) >> 1;
    // speed-up: if (ss[u] != idS)
    {
      ts[uL] = opST(ss[u], ts[uL], mid - l);
      ts[uR] = opST(ss[u], ts[uR], r - mid);
      ss[uL] = opSS(ss[u], ss[uL]);
      ss[uR] = opSS(ss[u], ss[uR]);
      ss[u] = idS;
    }
    const T resL = query(uL, l, mid, a, b, s);
    const T resR = query(uR, mid, r, a, b, s);
    ts[u] = opTT(ts[uL], ts[uR]);
    return opTT(resL, resR);
  }
};


// https://judge.yosupo.jp/problem/range_affine_range_sum

template<int M_> struct ModInt {
  static constexpr int M = M_;
  int x;
  constexpr ModInt() : x(0) {}
  constexpr ModInt(long long x_) : x(x_ % M) { if (x < 0) x += M; }
  ModInt &operator+=(const ModInt &a) { x += a.x; if (x >= M) x -= M; return *this; }
  ModInt &operator-=(const ModInt &a) { x -= a.x; if (x < 0) x += M; return *this; }
  ModInt &operator*=(const ModInt &a) { x = static_cast<int>((static_cast<long long>(x) * a.x) % M); return *this; }
  ModInt operator+(const ModInt &a) const { return (ModInt(*this) += a); }
  ModInt operator-(const ModInt &a) const { return (ModInt(*this) -= a); }
  ModInt operator*(const ModInt &a) const { return (ModInt(*this) *= a); }
  ModInt operator-() const { return ModInt(-x); }
  ModInt pow(long long e) const {
    ModInt x2 = x, xe = 1;
    for (; e; e >>= 1) {
      if (e & 1) xe *= x2;
      x2 *= x2;
    }
    return xe;
  }
  ModInt inv() const {
    int a = x, b = M, y = 1, z = 0, t;
    for (; ; ) {
      t = a / b; a -= t * b;
      if (a == 0) {
        assert(b == 1 || b == -1);
        return ModInt(b * z);
      }
      y -= t * z;
      t = b / a; b -= t * a;
      if (b == 0) {
        assert(a == 1 || a == -1);
        return ModInt(a * y);
      }
      z -= t * y;
    }
  }
  friend ModInt operator+(long long a, const ModInt &b) { return (ModInt(a) += b); }
  friend ModInt operator-(long long a, const ModInt &b) { return (ModInt(a) -= b); }
  friend ModInt operator*(long long a, const ModInt &b) { return (ModInt(a) *= b); }
  // friend std::ostream &operator<<(std::ostream &os, const ModInt &a) { return os << a.x; }
};

constexpr int MO = 998'244'353;
using Mint = ModInt<MO>;

int main() {
  struct Affine {
    Mint b, c;
  };
  const auto opTT = [](const Mint &t0, const Mint &t1) {
    return t0 + t1;
  };
  const auto opST = [](const Affine &s, const Mint &t, int sz) {
    return s.b * t + s.c * sz;
  };
  const auto opSS = [](const Affine &s0, const Affine &s1) {
    return Affine{s0.b * s1.b, s0.b * s1.c + s0.c};
  };

  int N, Q;
  for (; ~scanf("%d%d", &N, &Q); ) {
    SegmentTree<Mint, Affine, decltype(opTT), decltype(opST), decltype(opSS)>
        seg(N, opTT, opST, opSS, 0, {1, 0});
    for (int i = 0; i < N; ++i) {
      int a;
      scanf("%d", &a);
      seg.at(i) = a;
    }
    seg.build();
    for (int q = 0; q < Q; ++q) {
      int typ;
      scanf("%d", &typ);
      switch (typ) {
        case 0: {
          int l, r, b, c;
          scanf("%d%d%d%d", &l, &r, &b, &c);
          seg.query(l, r, {b, c});
        } break;
        case 1: {
          int l, r;
          scanf("%d%d", &l, &r);
          const Mint res = seg.query(l, r, seg.idS);
          printf("%d\n", res.x);
        } break;
        default: assert(false);
      }
    }
  }
  return 0;
}
