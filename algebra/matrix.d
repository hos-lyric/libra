import modint;

// det(x I + a)
// O(n^3)
T[] charPoly(T)(const(T[][]) a) {
  import std.algorithm.mutation : swap;
  const n = cast(int)(a.length);
  auto b = new T[][](n, n);
  foreach (i; 0 .. n) b[i][] = a[i][];
  // upper Hessenberg
  foreach (j; 0 .. n - 2) {
    foreach (i; j + 1 .. n) {
      if (b[i][j]) {
        swap(b[j + 1], b[i]);
        foreach (ii; 0 .. n) swap(b[ii][j + 1], b[ii][i]);
        break;
      }
    }
    if (b[j + 1][j]) {
      const r = 1 / b[j + 1][j];
      foreach (i; j + 2 .. n) {
        const s = r * b[i][j];
        foreach (jj; j .. n) b[i][jj] -= s * b[j + 1][jj];
        foreach (ii; 0 .. n) b[ii][j + 1] += s * b[ii][i];
      }
    }
  }
  // fss[i] := det(x I_i + b[0..i][0..i])
  auto fss = new T[][n + 1];
  fss[0] = [T(1)];
  foreach (i; 0 .. n) {
    fss[i + 1] = new T[i + 2];
    foreach (k; 0 .. i + 1) fss[i + 1][k + 1] = fss[i][k];
    foreach (k; 0 .. i + 1) fss[i + 1][k] += b[i][i] * fss[i][k];
    T prod = 1;
    foreach_reverse (j; 0 .. i) {
      prod *= -b[j + 1][j];
      const s = prod * b[j][i];
      foreach (k; 0 .. j + 1) fss[i + 1][k] += s * fss[j][k];
    }
  }
  return fss[n];
}

// det(x I + a), division free
// O(n^4)
T[] charPolyDivFree(T)(const(T[][]) a) {
  const n = cast(int)(a.length);
  auto ps = new T[n + 1];
  ps[n] = 1;
  foreach_reverse (h; 0 .. n) {
    // closed walks at h with repetition allowed from 0, ..., h - 1
    auto sub = new T[][](n, h + 1);
    foreach_reverse (i; 1 .. n + 1) {
      sub[i - 1][h] += ps[i];
    }
    foreach_reverse (i; 1 .. n) foreach (u; 0 .. h + 1) {
      foreach (v; 0 .. h) {
        sub[i - 1][v] -= sub[i][u] * a[u][v];
      }
    }
    foreach_reverse (i; 0 .. n) foreach (u; 0 .. h + 1) {
      ps[i] += sub[i][u] * a[u][h];
    }
  }
  return ps;
}


unittest {
  enum MO = 998244353;
  alias Mint = ModInt!MO;
  {
    const a = [
        [Mint(3), Mint(1), Mint(4)],
        [Mint(1), Mint(5), Mint(9)],
        [Mint(2), Mint(6), Mint(5)],
    ];
    const ps = charPoly(a);
    assert(ps.length == 3 + 1);
    assert(ps[0].x == MO - 90);
    assert(ps[1].x == MO - 8);
    assert(ps[2].x == 13);
    assert(ps[3].x == 1);
    assert(ps == charPolyDivFree(a));
  }
  {
    const a = [
        [Mint(3), Mint(-5), Mint(8), Mint(9)],
        [Mint(-7), Mint(9), Mint(-3), Mint(2)],
        [Mint(3), Mint(8), Mint(-4), Mint(-6)],
        [Mint(2), Mint(-6), Mint(4), Mint(3)],
    ];
    const ps = charPoly(a);
    assert(ps.length == 4 + 1);
    assert(ps[0].x == 181);
    assert(ps[1].x == MO - 171);
    assert(ps[2].x == MO - 14);
    assert(ps[3].x == 11);
    assert(ps[4].x == 1);
    assert(ps == charPolyDivFree(a));
  }
  {
    enum n = 100;
    auto a = new Mint[][](n, n);
    foreach (i; 0 .. n) foreach (j; 0 .. n) {
      a[i][j] = (i * j * j) % 199 - 100;
    }
    const ps = charPoly(a);
    assert(ps.length == n + 1);
    assert(ps[0].x == 0);
    assert(ps[1].x == 895461868);
    assert(ps[2].x == 863013394);
    assert(ps[49].x == 301922511);
    assert(ps[50].x == 222844028);
    assert(ps[51].x == 443314937);
    assert(ps[98].x == 997237804);
    assert(ps[99].x == 998243734);
    assert(ps[100].x == 1);
    assert(ps == charPolyDivFree(a));
  }
}

void main() {
}
