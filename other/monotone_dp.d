bool chmin(T)(ref T t, in T f) { if (t > f) { t = f; return true; } else { return false; } }

// Update g by g[i] := min{ g[i], min{ g[j] + f(j, i) | 0 <= j < i } }
//   i -> argmin{ g[j] + f(j, i) | 0 <= j < i } is increasing
void monotoneDP(T)(T[] g, in T delegate(int, int) f) {
  void update(int jL, int jR, int iL, int iR) {
    if (iL == iR) return;
    const iMid = (iL + iR) / 2;
    T opt = g[jL] + f(jL, iMid);
    int jOpt = jL;
    foreach (j; jL + 1 .. jR) if (chmin(opt, g[j] + f(j, iMid))) jOpt = j;
    chmin(g[iMid], opt);
    update(jL, jOpt + 1, iL, iMid);
    update(jOpt, jR, iMid + 1, iR);
  }
  void solve(int l, int r) {
    if (l + 1 == r) return;
    const mid = (l + r) / 2;
    solve(l, mid);
    update(l, mid, mid, r);
    solve(mid, r);
  }
  solve(0, cast(int)(g.length));
}

unittest {
  // https://yukicoder.me/problems/no/705
  import std.math : abs;
  long[] A = [0, 1, 2, 3];
  long[] X = [0, 1, 2, 3];
  long[] Y = [2, 2, 2, 2];
  long[] dp = [0, long.max, long.max, long.max, long.max];
  dp.monotoneDP((j, i) => abs(X[j] - A[i - 1])^^3 + abs(Y[j])^^3);
  assert(dp == [0, 8, 9, 16, 18]);
}

void main() {
}
