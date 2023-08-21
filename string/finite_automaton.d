// TODO: update as C++

class Dfa {
  int n, s, a;
  int[][] to;
  bool[] ac;
  this(int n, int s, int a) {
    this.n = n;
    this.s = s;
    this.a = a;
    to = new int[][](n, a);
    foreach (u; 0 .. n) to[u][] = -1;
    ac = new bool[n];
  }
  int addState() {
    const u = n++;
    to ~= new int[a];
    to[u][] = -1;
    ac ~= false;
    return u;
  }

  int[] ids;
  int[][] uss;
  int[][][] revs;
  Dfa minimize() {
    import std.algorithm.mutation : swap;
    foreach (u; 0 .. n) foreach (e; 0 .. a) {
      assert(to[u][e] != -1, "Dfa.minimize: to is not total.");
    }
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
    // empty
    if (uss[1].length == 0) {
      auto dfa = new Dfa(1, 0, a);
      dfa.to[0][] = 0;
      dfa.ac[0] = false;
      return dfa;
    }
    // all
    if (uss[0].length == 0) {
      auto dfa = new Dfa(1, 0, a);
      dfa.to[0][] = 0;
      dfa.ac[0] = true;
      return dfa;
    }
    qb = qe = 0;
    que[qe++] = (uss[1].length <= uss[0].length) ? 1 : 0;
    for (; qb != qe; ) {
      const x = que[qb++];
      bool[int] parter;
      foreach (u; uss[x]) parter[u] = true;
      foreach (e; 0 .. a) {
        bool[int] apps;
        foreach (u; parter.keys) foreach (v; revs[u][e]) apps[ids[v]] = true;
        foreach (y; apps.keys) {
          int[] vs1, vs0;
          foreach (v; uss[y]) ((to[v][e] in parter) ? vs1 : vs0) ~= v;
          assert(vs1.length > 0);
          if (vs0.length > 0) {
            if (vs1.length < vs0.length) swap(vs1, vs0);
            foreach (v; vs0) ids[v] = nn;
            que[qe++] = nn;
            uss[y] = vs1;
            uss[nn++] = vs0;
          }
        }
      }
    }
    uss.length = nn;
    // make new DFA
    auto dfa = new Dfa(nn, ids[s], a);
    foreach (x; 0 .. nn) {
      const u = uss[x][0];
      foreach (e; 0 .. a) dfa.to[x][e] = ids[to[u][e]];
      dfa.ac[x] = ac[u];
    }
    return dfa;
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
  foreach (u0; 0 .. n) {
    if (f01[u0] != -1 && dfa0.ac[u0] != dfa1.ac[f01[u0]]) return false;
  }
  return true;
}

class Nfa {
  int n, s, a;
  int[][][] to;
  int[][] eps;
  bool[] ac;
  this(int n, int s, int a) {
    this.n = n;
    this.s = s;
    this.a = a;
    to = new int[][][](n, a);
    eps = new int[][n];
    ac = new bool[n];
  }
  int addState() {
    const int u = n++;
    to ~= new int[][a];
    eps ~= [[]];
    ac ~= false;
    return u;
  }
  Dfa toDfa() const {
    import std.bigint : BigInt;
    import std.container.dlist : DList;
    DList!int que;
    auto epsed = new BigInt[n];
    foreach (u; 0 .. n) {
      epsed[u] |= BigInt(1) << u;
      que.insertBack(u);
      for (; !que.empty; ) {
        const v = que.front;
        que.removeFront;
        foreach (w; eps[v]) {
          if (!(epsed[u] & BigInt(1) << w)) {
            epsed[u] |= BigInt(1) << w;
            que.insertBack(w);
          }
        }
      }
    }
    auto dfa = new Dfa(1, 0, a);
    int nn;
    int[BigInt] tr;
    BigInt[] ps;
    que.insertBack(nn);
    ps ~= epsed[s];
    tr[epsed[s]] = nn++;
    for (; !que.empty; ) {
      const x = que.front;
      que.removeFront;
      foreach (e; 0 .. a) {
        BigInt pp;
        foreach (u; 0 .. n) {
          if (ps[x] & BigInt(1) << u) foreach (v; to[u][e]) pp |= epsed[v];
        }
        tr.update(pp, {
          dfa.addState;
          dfa.to[x][e] = nn;
          que.insertBack(nn);
          ps ~= pp;
          return nn++;
        }, (ref int y) {
          dfa.to[x][e] = y;
          return y;
        });
      }
    }
    foreach (x; 0 .. nn) foreach (u; 0 .. n) {
      if (ac[u] && (ps[x] & BigInt(1) << u)) dfa.ac[x] = true;
    }
    return dfa;
  }
}

// Dfa
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

// Dfa
unittest {
  // empty
  auto dfa0 = new Dfa(3, 0, 1);
  dfa0.to = [[1], [2], [0]];
  dfa0.ac[] = false;
  dfa0 = dfa0.minimize;
  assert(dfa0.n == 1);
  assert(dfa0.to == [[0]]);
  assert(dfa0.ac == [false]);
  // all
  auto dfa1 = new Dfa(3, 0, 1);
  dfa1.to = [[2], [0], [1]];
  dfa1.ac[] = true;
  dfa1 = dfa1.minimize;
  assert(dfa1.n == 1);
  assert(dfa1.to == [[0]]);
  assert(dfa1.ac == [true]);
}

// Nfa
unittest {
  // 0*10*(10*10*)* (odd number of 1's)
  auto nfa = new Nfa(6, 0, 2);
  nfa.to[0][0] ~= 0;
  nfa.to[0][1] ~= 1;
  nfa.to[1][0] ~= 1;
  nfa.to[3][1] ~= 4;
  nfa.to[4][0] ~= 4;
  nfa.to[4][1] ~= 5;
  nfa.to[5][0] ~= 5;
  nfa.eps[1] ~= 2;
  nfa.eps[2] ~= 3;
  nfa.eps[5] ~= 2;
  nfa.ac[2] = true;
  const minDfa = nfa.toDfa.minimize;
  auto dfa1 = new Dfa(2, 0, 2);
  dfa1.to = [[0, 1], [1, 0]];
  dfa1.ac = [false, true];
  assert(dfa1.isIsomorphic(minDfa));
  dfa1.ac = [true, false];
  assert(!dfa1.isIsomorphic(minDfa));
}

void main() {
}
