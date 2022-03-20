// root: min (tie-break: left)
class MinCartesianTree {
  int n, rt;
  int[] par, lef, rig;
  void build(T)(T as) {
    n = cast(int)(as.length);
    assert(n >= 1);
    rt = 0;
    par = new int[n]; par[] = -1;
    lef = new int[n]; lef[] = -1;
    rig = new int[n]; rig[] = -1;
    int top = 0;
    auto stack = new int[n];
    foreach (u; 1 .. n) {
      if (as[stack[top]] > as[u]) {  // >
        for (; top >= 1 && as[stack[top - 1]] > as[u]; --top) {}  // >
        if (top == 0) {
          rt = par[lef[u] = stack[top]] = u;
        } else {
          par[lef[u] = stack[top]] = u;
          rig[par[u] = stack[top - 1]] = u;
        }
        stack[top] = u;
      } else {
        rig[par[u] = stack[top]] = u;
        stack[++top] = u;
      }
    }
  }
};

// root: max (tie-break: left)
class MaxCartesianTree {
  int n, rt;
  int[] par, lef, rig;
  void build(T)(T as) {
    n = cast(int)(as.length);
    assert(n >= 1);
    rt = 0;
    par = new int[n]; par[] = -1;
    lef = new int[n]; lef[] = -1;
    rig = new int[n]; rig[] = -1;
    int top = 0;
    auto stack = new int[n];
    foreach (u; 1 .. n) {
      if (as[stack[top]] < as[u]) {  // <
        for (; top >= 1 && as[stack[top - 1]] < as[u]; --top) {}  // <
        if (top == 0) {
          rt = par[lef[u] = stack[top]] = u;
        } else {
          par[lef[u] = stack[top]] = u;
          rig[par[u] = stack[top - 1]] = u;
        }
        stack[top] = u;
      } else {
        rig[par[u] = stack[top]] = u;
        stack[++top] = u;
      }
    }
  }
};

////////////////////////////////////////////////////////////////////////////////

// min
unittest {
  void check(T)(T as, MinCartesianTree ct) {
    assert(0 <= ct.rt); assert(ct.rt < ct.n);
    assert(ct.par.length == ct.n);
    assert(ct.lef.length == ct.n);
    assert(ct.rig.length == ct.n);
    assert(ct.par[ct.rt] == -1);
    foreach (u; 0 .. ct.n) {
      if (u != ct.rt) {
        const int p = ct.par[u];
        assert(0 <= p); assert(p < ct.n);
        assert(ct.lef[p] == u || ct.rig[p] == u);
      }
      const int l = ct.lef[u];
      if (l != -1) {
        assert(0 <= l); assert(l < u);
        assert(u == ct.par[l]);
        assert(as[l] > as[u]);
      }
      const int r = ct.rig[u];
      if (r != -1) {
        assert(u < r); assert(r < ct.n);
        assert(u == ct.par[r]);
        assert(as[u] <= as[r]);
      }
    }
  }
  {
    const long[7] as = [3, 1, 4, 1, 5, 9, 2];
    auto ct = new MinCartesianTree;
    ct.build(as);
    assert(ct.n == 7);
    assert(ct.rt == 1);
    assert(ct.par == [1, -1, 3, 1, 6, 4, 3]);
    assert(ct.lef == [-1, 0, -1, 2, -1, -1, 4]);
    assert(ct.rig == [-1, 3, -1, 6, 5, -1, -1]);
    check(as, ct);
  }
  
  foreach (n; 1 .. 6 + 1) {
    foreach (p; 0 .. n^^n) {
      auto as = new int[n];
      foreach (i; 0 .. n) {
        as[i] = p / n^^i % n;
      }
      auto ct = new MinCartesianTree;
      ct.build(as);
      check(as, ct);
    }
  }
}

// max
unittest {
  void check(T)(T as, MaxCartesianTree ct) {
    assert(0 <= ct.rt); assert(ct.rt < ct.n);
    assert(ct.par.length == ct.n);
    assert(ct.lef.length == ct.n);
    assert(ct.rig.length == ct.n);
    assert(ct.par[ct.rt] == -1);
    foreach (u; 0 .. ct.n) {
      if (u != ct.rt) {
        const int p = ct.par[u];
        assert(0 <= p); assert(p < ct.n);
        assert(ct.lef[p] == u || ct.rig[p] == u);
      }
      const int l = ct.lef[u];
      if (l != -1) {
        assert(0 <= l); assert(l < u);
        assert(u == ct.par[l]);
        assert(as[l] < as[u]);
      }
      const int r = ct.rig[u];
      if (r != -1) {
        assert(u < r); assert(r < ct.n);
        assert(u == ct.par[r]);
        assert(as[u] >= as[r]);
      }
    }
  }
  {
    const long[7] as = [3, 1, 4, 1, 5, 9, 2];
    auto ct = new MaxCartesianTree;
    ct.build(as);
    assert(ct.n == 7);
    assert(ct.rt == 5);
    assert(ct.par == [2, 0, 4, 2, 5, -1, 5]);
    assert(ct.lef == [-1, -1, 0, -1, 2, 4, -1]);
    assert(ct.rig == [1, -1, 3, -1, -1, 6, -1]);
    check(as, ct);
  }
  
  foreach (n; 1 .. 6 + 1) {
    foreach (p; 0 .. n^^n) {
      auto as = new int[n];
      foreach (i; 0 .. n) {
        as[i] = p / n^^i % n;
      }
      auto ct = new MaxCartesianTree;
      ct.build(as);
      check(as, ct);
    }
  }
}

// https://judge.yosupo.jp/problem/cartesian_tree
import core.stdc.stdio;
import std.stdio;
void yosupoMin_cartesian_tree() {
  int N;
  for (; ~scanf("%d", &N); ) {
    auto A = new int[N];
    foreach (u; 0 .. N) {
      scanf("%d", &A[u]);
    }
    auto ct = new MinCartesianTree;
    ct.build(A);
    foreach (u; 0 .. N) {
      if (u) write(" ");
      write((u == ct.rt) ? u : ct.par[u]);
    }
    writeln;
  }
}
void yosupoMax_cartesian_tree() {
  int N;
  for (; ~scanf("%d", &N); ) {
    auto A = new int[N];
    foreach (u; 0 .. N) {
      scanf("%d", &A[u]);
    }
    auto ct = new MinCartesianTree;
    ct.build(A);
    foreach (u; 0 .. N) {
      if (u) write(" ");
      write((u == ct.rt) ? u : ct.par[u]);
    }
    writeln;
  }
}

void main() {
  // yosupoMin_cartesian_tree();
  // yosupoMax_cartesian_tree();
}
