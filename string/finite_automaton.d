class Dfa {
  int n, s, a;
  int[][] to;
  bool[] ac;
  this(int n, int s, int a) {
    this.n = n;
    this.s = s;
    this.a = a;
    to = new int[][](n, a);
    foreach (u; 0 .. n) {
      to[u][] = -1;
    }
    ac = new bool[n];
  }

  int[] ids;
  int[][] uss;
  int[][][] revs;
  Dfa minimize() {
    import std.algorithm.mutation : swap;
    auto que = new int[n];
    int qb, qe;
    ids = new int[n];
    ids[] = -1;
    // BFS to find reachable states
    qb = qe = 0;
    ids[que[qe++] = s] = -2;
    for (; qb != qe; ) {
      const u = que[qb++];
      foreach (e; 0 .. a) {
        if (ids[to[u][e]] == -1) ids[que[qe++] = to[u][e]] = -2;
      }
    }
    // partition
    revs = new int[][][](n, a);
    foreach (u; 0 .. n) {
      if (ids[u] != -1) foreach (e; 0 .. a) revs[to[u][e]][e] ~= u;
    }
    int nn = 2;
    uss = new int[][n];
    foreach (u; 0 .. n) if (ids[u] == -2) uss[ids[u] = ac[u] ? 1 : 0] ~= u;
    qb = qe = 0;
    auto on = new bool[n];
    on[que[qe++] = (uss[1].length <= uss[0].length) ? 1 : 0] = true;
    for (; qb != qe; ) {
      const x = que[qb++];
      on[x] = false;
      foreach (e; 0 .. a) {
        bool[int] apps;
        foreach (u; uss[x]) foreach (v; revs[u][e]) apps[ids[v]] = true;
        foreach (y; apps.keys) {
          int[] vs1, vs0;
          foreach (v; uss[y]) ((ids[to[v][e]] == x) ? vs1 : vs0) ~= v;
          assert(vs1.length > 0);
          if (vs0.length > 0) {
            if (vs1.length > vs0.length) swap(vs1, vs0);
            foreach (v; vs0) ids[v] = nn;
            uss[y] = vs1;
            uss[nn++] = vs0;
            if (!on[y]) on[que[qe++] = y] = true;
          }
        }
      }
    }
    uss.length = nn;
    // make new DFA
    auto ret = new Dfa(nn, ids[s], a);
    foreach (x; 0 .. nn) {
      const u = uss[x][0];
      foreach (e; 0 .. a) ret.to[x][e] = ids[to[u][e]];
      ret.ac[x] = ac[u];
    }
    return ret;
  }
}

bool isIsomorphic(const(Dfa) dfa0, const(Dfa) dfa1) {
  if (dfa0.n != dfa1.n) return false;
  if (dfa0.a != dfa1.a) return false;
  const n = dfa0.n, a = dfa0.a;
  auto f01 = new int[n], f10 = new int[n];
  f01[] = -1;
  f10[] = -1;
  auto que = new int[2 * n];
  int qb, qe;
  f10[f01[dfa0.s] = dfa1.s] = dfa0.s;
  que[qe++] = dfa0.s;
  que[qe++] = dfa1.s;
  for (; qb != qe; ) {
    const u0 = que[qb++];
    const u1 = que[qb++];
    foreach (e; 0 .. a) {
      const v0 = dfa0.to[u0][e], v1 = dfa1.to[u1][e];
      if (f01[v0] == -1 && f10[v1] == -1) {
        f10[f01[v0] = v1] = v0;
        que[qe++] = v0;
        que[qe++] = v1;
      } else {
        if (f01[v0] == -1 || f10[v1] == -1) return false;
        if (f10[f01[v0]] != v0 || f01[f10[v1]] != v1) return false;
      }
    }
  }
  foreach (u0; 0 .. n) if (dfa0.ac[u0] != dfa1.ac[f01[u0]]) return false;
  return true;
}

// DFA
unittest {
  // https://www.cs.wcupa.edu/rkline/fcs/dfa-min.html
  auto dfa = new Dfa(7, 1, 2);
  dfa.to = [[1, 2], [2, 4], [5, 3], [2, 6], [1, 5], [5, 5], [3, 5]];
  dfa.ac[1] = dfa.ac[3] = true;
  const minDfa = dfa.minimize;
  assert(dfa.ids[0] == -1);
  assert(dfa.ids[1] == dfa.ids[3]);
  assert(dfa.ids[4] == dfa.ids[6]);
  assert(minDfa.n == 4);
  assert(minDfa.s == dfa.ids[1]);
  assert(minDfa.a == 2);
  assert(minDfa.to[dfa.ids[1]] == [dfa.ids[2], dfa.ids[4]]);
  assert(minDfa.to[dfa.ids[2]] == [dfa.ids[5], dfa.ids[1]]);
  assert(minDfa.to[dfa.ids[4]] == [dfa.ids[1], dfa.ids[5]]);
  assert(minDfa.to[dfa.ids[5]] == [dfa.ids[5], dfa.ids[5]]);
  assert(minDfa.ac[dfa.ids[1]]);
  assert(!minDfa.ac[dfa.ids[2]]);
  assert(!minDfa.ac[dfa.ids[4]]);
  assert(!minDfa.ac[dfa.ids[5]]);
  auto dfa1 = new Dfa(4, 0, 2);
  dfa1.to = [[1, 2], [3, 0], [0, 3], [3, 3]];
  dfa1.ac[0] = true;
  assert(minDfa.isIsomorphic(dfa1));
}

void main() {
}
