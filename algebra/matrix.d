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

// det(a + x b)
// O(n^3)
T[] detPoly(T)(const(T[][]) a_, const(T[][]) b_) {
  import std.algorithm.mutation : swap;
  const n = cast(int)(a_.length);
  auto a = new T[][](n, n), b = new T[][](n, n);
  foreach (i; 0 .. n) a[i][] = a_[i][];
  foreach (i; 0 .. n) b[i][] = b_[i][];
  T prod = 1;
  int off = 0;
  foreach (h; 0 .. n) {
    for (; ; ) {
      if (b[h][h]) break;
      foreach (j; h + 1 .. n) {
        if (b[h][j]) {
          prod *= -1;
          foreach (i; 0 .. n) {
            swap(a[i][h], a[i][j]);
            swap(b[i][h], b[i][j]);
          }
          break;
        }
      }
      if (b[h][h]) break;
      if (++off > n) {
        auto gs = new T[n + 1];
        gs[] = T(0);
        return gs;
      }
      foreach (j; 0 .. n) {
        b[h][j] = a[h][j];
        a[h][j] = 0;
      }
      foreach (i; 0 .. h) {
        const T t = b[h][i];
        foreach (j; 0 .. n) {
          a[h][j] -= t * a[i][j];
          b[h][j] -= t * b[i][j];
        }
      }
    }
    prod *= b[h][h];
    const T s = 1 / b[h][h];
    foreach (j; 0 .. n) {
      a[h][j] *= s;
      b[h][j] *= s;
    }
    foreach (i; 0 .. n) if (h != i) {
      const T t = b[i][h];
      foreach (j; 0 .. n) {
        a[i][j] -= t * a[h][j];
        b[i][j] -= t * b[h][j];
      }
    }
  }
  const fs = charPoly(a);
  auto gs = new T[n + 1];
  gs[] = T(0);
  foreach (i; 0 .. n - off + 1) gs[i] = prod * fs[off + i];
  return gs;
}

// det(a[0] + x a[1] + ... + x^m a[m])
// O((m n)^3)
T[] detPoly(T)(const(T[][][]) a_) {
  assert(a_.length != 0, "[detPoly] T[][][] a must not be empty");
  import std.algorithm.mutation : swap;
  const m = cast(int)(a_.length) - 1, n = cast(int)(a_[0].length);
  auto a = new T[][][](m + 1, n, n);
  foreach (d; 0 .. m + 1) foreach (i; 0 .. n) a[d][i][] = a_[d][i][];
  T prod = 1;
  int off = 0;
  foreach (h; 0 .. n) {
    for (; ; ) {
      if (a[m][h][h]) break;
      foreach (j; h + 1 .. n) {
        if (a[m][h][j]) {
          prod *= -1;
          foreach (d; 0 .. m + 1) foreach (i; 0 .. n) {
            swap(a[d][i][h], a[d][i][j]);
          }
          break;
        }
      }
      if (a[m][h][h]) break;
      if (++off > m * n) {
        auto gs = new T[m * n + 1];
        gs[] = T(0);
        return gs;
      }
      foreach_reverse (d; 0 .. m) foreach (j; 0 .. n) {
        a[d + 1][h][j] = a[d][h][j];
      }
      foreach (j; 0 .. n) {
        a[0][h][j] = 0;
      }
      foreach (i; 0 .. h) {
        const T t = a[m][h][i];
        foreach (d; 0 .. m + 1) foreach (j; 0 .. n) {
          a[d][h][j] -= t * a[d][i][j];
        }
      }
    }
    prod *= a[m][h][h];
    const T s = 1 / a[m][h][h];
    foreach (d; 0 .. m + 1) foreach (j; 0 .. n) {
      a[d][h][j] *= s;
    }
    foreach (i; 0 .. n) if (h != i) {
      const T t = a[m][i][h];
      foreach (d; 0 .. m + 1) foreach (j; 0 .. n) {
        a[d][i][j] -= t * a[d][h][j];
      }
    }
  }
  auto b = new T[][](m * n, m * n);
  foreach (i; 0 .. n) b[i][] = T(0);
  foreach (i; 0 .. (m - 1) * n) b[i][n + i] = -1;
  foreach (d; 0 .. m) foreach (i; 0 .. n) foreach (j; 0 .. n) {
    b[(m - 1) * n + i][d * n + j] = a[d][i][j];
  }
  const fs = charPoly(b);
  auto gs = new T[m * n + 1];
  gs[] = T(0);
  foreach (i; 0 .. m * n - off + 1) gs[i] = prod * fs[off + i];
  return gs;
}


// TODO: rankDecompose

////////////////////////////////////////////////////////////////////////////////

unittest {
  enum MO = 998244353;
  alias Mint = ModInt!MO;

  // charPolyDivFree, charPoly
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

  // detPoly
  {
    const(Mint[][]) a, b;
    const ps = detPoly(a, b);
    assert(ps.length == 0 + 1);
    assert(ps[0].x == 1);
    assert(ps == detPoly([a, b]));
  }
  {
    const a = [[Mint(20)]];
    const b = [[Mint(33)]];
    const ps = detPoly(a, b);
    assert(ps.length == 1 + 1);
    assert(ps[0].x == 20);
    assert(ps[1].x == 33);
    assert(ps == detPoly([a, b]));
  }
  {
    const a = [
        [Mint(3), Mint(1), Mint(4)],
        [Mint(1), Mint(5), Mint(9)],
        [Mint(2), Mint(6), Mint(5)],
    ];
    const b = [
        [Mint(3), Mint(5), Mint(8)],
        [Mint(9), Mint(7), Mint(9)],
        [Mint(3), Mint(2), Mint(3)],
    ];
    const ps = detPoly(a, b);
    assert(ps.length == 3 + 1);
    assert(ps[0].x == MO - 90);
    assert(ps[1].x == MO - 15);
    assert(ps[2].x == 132);
    assert(ps[3].x == MO - 15);
    assert(ps == detPoly([a, b]));
  }
  {
    const a = [
        [Mint(3), Mint(1), Mint(4)],
        [Mint(1), Mint(5), Mint(9)],
        [Mint(2), Mint(6), Mint(5)],
    ];
    const b = [
        [Mint(3), Mint(5), Mint(8)],
        [Mint(9), Mint(7), Mint(9)],
        [Mint(6), Mint(2), Mint(1)],
    ];
    const ps = detPoly(a, b);
    assert(ps.length == 3 + 1);
    assert(ps[0].x == MO - 90);
    assert(ps[1].x == MO - 76);
    assert(ps[2].x == 46);
    assert(ps[3].x == 0);
    assert(ps == detPoly([a, b]));
  }
  {
    const a = [
        [Mint(1), Mint(2), Mint(3), Mint(-5)],
        [Mint(8), Mint(-3), Mint(1), Mint(-4)],
        [Mint(5), Mint(9), Mint(-4), Mint(-3)],
        [Mint(-7), Mint(0), Mint(-7), Mint(-7)],
    ];
    const b = [
        [Mint(0), Mint(0), Mint(1), Mint(2)],
        [Mint(0), Mint(0), Mint(3), Mint(4)],
        [Mint(5), Mint(6), Mint(7), Mint(8)],
        [Mint(10), Mint(12), Mint(4), Mint(6)],
    ];
    const ps = detPoly(a, b);
    assert(ps.length == 4 + 1);
    assert(ps[0].x == MO - 6356);
    assert(ps[1].x == 7362);
    assert(ps[2].x == MO - 5875);
    assert(ps[3].x == 646);
    assert(ps[4].x == 0);
    assert(ps == detPoly([a, b]));
  }
  {
    const a = [
        [
            [Mint(2), Mint(0), Mint(3)],
            [Mint(0), Mint(4), Mint(8)],
            [Mint(1), Mint(5), Mint(4)],
        ], [
            [Mint(-1), Mint(-2), Mint(-9)],
            [Mint(-7), Mint(3), Mint(4)],
            [Mint(8), Mint(6), Mint(-5)],
        ], [
            [Mint(2), Mint(4), Mint(7)],
            [Mint(8), Mint(6), Mint(8)],
            [Mint(5), Mint(1), Mint(0)],
        ]
    ];
    const ps = detPoly(a);
    assert(ps.length == 6 + 1);
    assert(ps[0].x == MO - 60);
    assert(ps[1].x == MO - 318);
    assert(ps[2].x == 188);
    assert(ps[3].x == 17);
    assert(ps[4].x == MO - 488);
    assert(ps[5].x == 304);
    assert(ps[6].x == MO - 10);
  }
  {
    const a = [
        [
            [Mint(2), Mint(0), Mint(3)],
            [Mint(0), Mint(4), Mint(8)],
            [Mint(1), Mint(5), Mint(4)],
        ], [
            [Mint(-1), Mint(-2), Mint(-9)],
            [Mint(-7), Mint(3), Mint(4)],
            [Mint(8), Mint(-1), Mint(5)],
        ], [
            [Mint(12), Mint(8), Mint(12)],
            [Mint(8), Mint(6), Mint(8)],
            [Mint(-16), Mint(-12), Mint(-16)],
        ]
    ];
    const ps = detPoly(a);
    assert(ps.length == 6 + 1);
    assert(ps[0].x == MO - 60);
    assert(ps[1].x == MO - 126);
    assert(ps[2].x == 459);
    assert(ps[3].x == MO - 122);
    assert(ps[4].x == 294);
    assert(ps[5].x == 152);
    assert(ps[6].x == 0);
  }
  {
    const a = [
        [
            [Mint(0), Mint(0), Mint(0), Mint(0)],
            [Mint(0), Mint(0), Mint(0), Mint(0)],
            [Mint(0), Mint(0), Mint(0), Mint(0)],
            [Mint(0), Mint(0), Mint(0), Mint(0)],
        ], [
            [Mint(0), Mint(1), Mint(0), Mint(0)],
            [Mint(0), Mint(0), Mint(1), Mint(0)],
            [Mint(0), Mint(1), Mint(0), Mint(0)],
            [Mint(0), Mint(0), Mint(0), Mint(1)],
        ], [
            [Mint(0), Mint(0), Mint(0), Mint(1)],
            [Mint(0), Mint(1), Mint(1), Mint(0)],
            [Mint(0), Mint(0), Mint(0), Mint(0)],
            [Mint(0), Mint(1), Mint(0), Mint(0)],
        ], [
            [Mint(1), Mint(0), Mint(0), Mint(0)],
            [Mint(0), Mint(1), Mint(1), Mint(0)],
            [Mint(1), Mint(1), Mint(0), Mint(0)],
            [Mint(0), Mint(0), Mint(0), Mint(1)],
        ], [
            [Mint(0), Mint(0), Mint(0), Mint(1)],
            [Mint(0), Mint(0), Mint(1), Mint(0)],
            [Mint(0), Mint(1), Mint(0), Mint(1)],
            [Mint(0), Mint(1), Mint(1), Mint(0)],
        ], [
            [Mint(0), Mint(0), Mint(0), Mint(0)],
            [Mint(0), Mint(0), Mint(0), Mint(0)],
            [Mint(0), Mint(0), Mint(0), Mint(0)],
            [Mint(0), Mint(0), Mint(0), Mint(0)],
        ]
    ];
    const ps = detPoly(a);
    assert(ps.length == 20 + 1);
    assert(ps[0].x == 0);
    assert(ps[1].x == 0);
    assert(ps[2].x == 0);
    assert(ps[3].x == 0);
    assert(ps[4].x == 0);
    assert(ps[5].x == 0);
    assert(ps[6].x == 0);
    assert(ps[7].x == 0);
    assert(ps[8].x == MO - 2);
    assert(ps[9].x == MO - 3);
    assert(ps[10].x == MO - 5);
    assert(ps[11].x == MO - 5);
    assert(ps[12].x == MO - 3);
    assert(ps[13].x == MO - 3);
    assert(ps[14].x == MO - 1);
    assert(ps[15].x == 0);
    assert(ps[16].x == 0);
    assert(ps[17].x == 0);
    assert(ps[18].x == 0);
    assert(ps[19].x == 0);
    assert(ps[20].x == 0);
  }
}

void main() {
}
