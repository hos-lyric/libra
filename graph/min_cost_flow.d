import std.algorithm, std.range;
bool chmax(T)(ref T t, in T f) { if (t < f) { t = f; return true; } else { return false; } }

class MinCostFlow(wint, cint) {
  int n, m;
  int[][] g;
  int[] zu;
  wint[] capa0, capa, ex;
  cint[] cost;
  real[] pot;
  bool[] vis;
  int[] itr, lev;
  this(int n) {
    this.n = n; m = 0; g = new int[][n]; zu = null; capa = null; cost = null;
    ex = new wint[n]; pot = new real[n]; pot[] = 0; vis = new bool[n]; itr = new int[n]; lev = new int[n];
  }
  void addEdge(int u, int v, wint w, cint c) {
    g[u] ~= m; zu ~= v; capa0 ~= w; capa ~= w; cost ~= +c; ++m;
    g[v] ~= m; zu ~= u; capa0 ~= 0; capa ~= 0; cost ~= -c; ++m;
  }
  wint augment(int u, int t, wint f) {
    if (u == t) return f;
    foreach (i; g[u][itr[u] .. $]) {
      if (capa[i] > 0 && lev[u] < lev[zu[i]]) {
        wint g = augment(zu[i], t, min(f, capa[i]));
        if (g > 0) {
          capa[i] -= g; capa[i ^ 1] += g; return g;
        }
      }
      ++itr[u];
    }
    return 0;
  }
  wint augment(int u, wint f) {
    if (ex[u] < 0) {
      wint g = min(f, -ex[u]); ex[u] += g; return g;
    }
    foreach (i; g[u][itr[u] .. $]) {
      if (capa[i] > 0 && cost[i] + pot[u] - pot[zu[i]] < 0) {
        wint g = augment(zu[i], min(f, capa[i]));
        if (g > 0) {
          capa[i] -= g; capa[i ^ 1] += g; return g;
        }
      }
      ++itr[u];
    }
    return 0;
  }
  wint dinic(int s, int t, wint f) {
    wint tof = 0;
    for (; tof < f; ) {
      int[] q;
      lev[] = -1;
      for (lev[s] = 0, q ~= s; !q.empty; ) {
        int u = q.front; q.popFront;
        foreach (i; g[u]) {
          int v = zu[i];
          if (capa[i] > 0 && lev[v] == -1) {
            lev[v] = lev[u] + 1; q ~= v;
          }
        }
      }
      if (lev[t] == -1) break;
      itr[] = 0;
      for (wint g; (g = augment(s, t, f - tof)) > 0; ) tof += g;
    }
    return tof;
  }
  void dfs(int u) {
    if (vis[u]) return; vis[u] = true;
    foreach (i; g[u]) if (capa[i] > 0 && cost[i] + pot[u] - pot[zu[i]] < 0) {
      dfs(zu[i]);
    }
  }
  cint solve() {
    real eps = 0;
  // cint solve(int s, int t, wint flow) {
    // real eps = 1;
    // ex[s] += flow;
    // ex[t] -= flow;
    foreach (i; 0 .. m) if (capa[i] > 0) chmax(eps, cast(real)(-cost[i]));
    for (; eps * n >= 1; ) {
      eps /= 4;
      foreach (i; 0 .. m) if (capa[i] > 0 && cost[i] + pot[zu[i ^ 1]] - pot[zu[i]] < 0) {
        ex[zu[i ^ 1]] -= capa[i]; ex[zu[i]] += capa[i]; capa[i ^ 1] += capa[i]; capa[i] = 0;
      }
      for (; ; ) {
        vis[] = false; itr[] = 0;
        foreach (u; 0 .. n) if (ex[u] > 0) dfs(u);
        foreach (u; 0 .. n) if (vis[u]) pot[u] -= eps;
        foreach (u; 0 .. n) for (wint f; ex[u] > 0 && (f = augment(u, ex[u])) > 0; ) ex[u] -= f;
        if (ex.all!"a <= 0") break;
      }
    }
    cint toc = 0;
    foreach (i; 0 .. m) if (capa0[i] > capa[i]) toc += (capa0[i] - capa[i]) * cost[i];
    return toc;
  }
}

unittest {
  // https://judge.yosupo.jp/problem/min_cost_b_flow
  {
    long ans;
    auto mcf = new MinCostFlow!(long, long)(3);
    void ae(int u, int v, long cL, long cU, long d) {
      ans += cL * d;
      mcf.ex[u] += cL;
      mcf.ex[v] -= cL;
      mcf.addEdge(u, v, cU - cL, d);
    }
    mcf.ex = [1, 0, -1];
    ae(0, 1, 1, 2, 1);
    ae(1, 2, 0, 2, 2);
    ae(2, 0, -3, 5, 1);
    ae(0, 2, 0, 3, -2);
    ae(2, 1, 0, 1, 0);
    ans += mcf.solve;
    assert(ans == -2);
  }
}

void main() {
}
