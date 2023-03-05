// directed, cannot distinguish the outgoing edges
class Bisimulation {
  import std.algorithm : sort, swap;

  int n;
  int[][] graph, hparg;

  int nn;
  int[] ids;
  int[][] uss;

  this(int n_) {
    n = n_;
    graph = new int[][n];
    hparg = new int[][n];
    nn = -1;
  }
  void ae(int u, int v) {
    assert(0 <= u, "[Bisimulation.ae] 0 <= u must hold.");
    assert(u < n, "[Bisimulation.ae] u < n must hold.");
    assert(0 <= v, "[Bisimulation.ae] 0 <= v must hold.");
    assert(v < n, "[Bisimulation.ae] v < n must hold.");
    graph[u] ~= v;
    hparg[v] ~= u;
  }
  void run() {
    // separate by degree
    int maxDeg = 0;
    foreach (u; 0 .. n) if (maxDeg < graph[u].length) maxDeg = cast(int)(graph[u].length);
    uss = new int[][maxDeg + 1];
    foreach (u; 0 .. n) uss[graph[u].length] ~= u;
    uss.sort!((us0, us1) => (us0.length > us1.length));
    nn = 0;
    foreach (d; 0 .. maxDeg + 1) if (uss[d].length != 0) ++nn;
    ids = new int[n];
    auto poss = new int[n];
    foreach (x; 0 .. nn) {
      int pos = 0;
      foreach (u; uss[x]) {
        ids[u] = x;
        poss[u] = pos++;
      }
    }
    // uss as queue
    uss.length = n;
    // vertex to move (reused)
    auto deg = new int[n];
    auto wss = new int[][n];
    for (int x = 1; x < nn; ++x) {
      // partition by degree to uss[x]
      int[] ys;
      foreach (u; uss[x]) foreach (v; hparg[u]) {
        const y = ids[v];
        if (wss[y].length == 0) ys ~= y;
        if (deg[v]++ == 0) wss[y] ~= v;
      }
      foreach (y; ys) {
        maxDeg = 0;
        foreach (v; wss[y]) if (maxDeg < deg[v]) maxDeg = deg[v];
        auto vss = new int[][maxDeg + 1];
        vss[0] = uss[y];
        foreach (v; wss[y]) {
          // move v from vss[0] to vss[deg[v]]
          swap(vss[0][poss[v]], vss[0][$ - 1]);
          poss[vss[0][poss[v]]] = poss[v];
          vss[0].length -= 1;
          poss[v] = cast(int)(vss[deg[v]].length);
          vss[deg[v]] ~= v;
        }
        int dm = 0;
        foreach (d; 1 .. maxDeg + 1) if (vss[dm].length < vss[d].length) dm = d;
        if (dm != 0) foreach (v; vss[dm]) ids[v] = y;
        uss[y] = vss[dm];
        foreach (d; 0 .. maxDeg + 1) if (vss[d].length != 0 && dm != d) {
          const z = nn++;
          uss[z] = vss[d];
          foreach (v; uss[z]) ids[v] = z;
        }
      }
      foreach (y; ys) {
        foreach (v; wss[y]) deg[v] = 0;
        wss[y] = [];
      }
    }
    uss.length = nn;
    // to make the output unique
    uss.sort;
    foreach (x; 0 .. nn) {
      uss[x].sort;
      foreach (u; uss[x]) ids[u] = x;
    }
  }
};

////////////////////////////////////////////////////////////////////////////////

unittest {
  {
    auto b = new Bisimulation(10);
    b.ae(0, 1);
    b.ae(0, 1);
    b.ae(1, 2);
    b.ae(2, 3);
    b.ae(2, 3);
    b.ae(3, 0);
    b.ae(4, 5);
    b.ae(4, 5);
    b.ae(5, 6);
    b.ae(6, 7);
    b.ae(6, 7);
    b.ae(7, 8);
    b.ae(8, 9);
    b.ae(8, 9);
    b.ae(9, 4);
    b.run();
    assert(b.nn == 2);
    assert(b.ids == [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]);
    assert(b.uss == [[0, 2, 4, 6, 8], [1, 3, 5, 7, 9]]);
  }
  {
    auto b = new Bisimulation(8);
    b.ae(0, 1);
    b.ae(1, 2);
    b.ae(2, 3);
    b.ae(3, 4);
    b.ae(4, 5);
    b.ae(5, 6);
    b.ae(6, 7);
    b.run();
    assert(b.nn == 8);
    assert(b.ids == [0, 1, 2, 3, 4, 5, 6, 7]);
    assert(b.uss == [[0], [1], [2], [3], [4], [5], [6], [7]]);
  }
  {
    auto b = new Bisimulation(3);
    b.ae(1, 2);
    b.ae(1, 2);
    b.ae(1, 2);
    b.ae(1, 2);
    b.ae(1, 2);
    b.ae(2, 1);
    b.ae(2, 1);
    b.ae(2, 1);
    b.ae(2, 1);
    b.ae(2, 1);
    b.run();
    assert(b.nn == 2);
    assert(b.ids == [0, 1, 1]);
    assert(b.uss == [[0], [1, 2]]);
  }
  {
    // 0: [1, 2, 3], 1: [1, 2, 2], 2: [1, 1, 3], 3: [2, 2]
    auto b = new Bisimulation(9);
    b.ae(0, 1); b.ae(0, 2); b.ae(0, 4);
    b.ae(1, 1); b.ae(1, 5); b.ae(1, 7);
    b.ae(2, 1); b.ae(2, 1); b.ae(2, 8);
    b.ae(3, 1); b.ae(3, 5); b.ae(3, 8);
    b.ae(4, 2); b.ae(4, 5);
    b.ae(5, 1); b.ae(5, 1); b.ae(5, 4);
    b.ae(6, 1); b.ae(6, 2); b.ae(6, 8);
    b.ae(7, 1); b.ae(7, 1); b.ae(7, 4);
    b.ae(8, 5); b.ae(8, 5);
    b.run();
    assert(b.nn == 4);
    assert(b.ids == [0, 1, 2, 0, 3, 2, 0, 2, 3]);
    assert(b.uss == [[0, 3, 6], [1], [2, 5, 7], [4, 8]]);
  }
}

void main() {
}
