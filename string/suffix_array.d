struct SuffixArray(T) {
  import std.algorithm : sort;
  int n;
  T[] ts;
  int[] us, su, lcp;
  this(T)(T[] ts) {
    n = cast(int)(ts.length);
    this.ts = ts;
    us = new int[n + 1];
    su = new int[n + 1];
    foreach (i; 0 .. n + 1) us[i] = i;
    us.sort!((u, v) => (cmp(u, v) < 0));
    auto vals = new int[n + 1], cnt = new int[n + 1], tmp = new int[n + 1];
    foreach (i; 0 .. n) vals[i + 1] = vals[i] + ((cmp(us[i], us[i + 1]) < 0) ? 1 : 0);
    for (int h = 1; ; h <<= 1) {
      int ahead(int i) {
        return (us[i] + h <= n) ? su[us[i] + h] : 0;
      }
      foreach (i; 0 .. n + 1) su[us[i]] = vals[i];
      if (vals[n] == n) break;
      cnt[] = 0;
      foreach (i; 0 .. n + 1) ++cnt[ahead(i)];
      foreach (j; 0 .. n) cnt[j + 1] += cnt[j];
      foreach_reverse (i; 0 .. n + 1) tmp[--cnt[ahead(i)]] = us[i];
      cnt[] = 0;
      foreach (i; 0 .. n + 1) ++cnt[su[tmp[i]]];
      foreach (j; 0 .. n) cnt[j + 1] += cnt[j];
      foreach_reverse (i; 0 .. n + 1) us[--cnt[su[tmp[i]]]] = tmp[i];
      foreach (i; 0 .. n) vals[i + 1] = vals[i] + ((su[us[i]] < su[us[i + 1]] || ahead(i) < ahead(i + 1)) ? 1 : 0);
    }
    lcp = new int[n];
    int h;
    foreach (u; 0 .. n) {
      for (int v = us[su[u] - 1]; cmp(u + h, v + h) == 0; ++h) {}
      lcp[su[u] - 1] = h;
      if (h > 0) --h;
    }
  }
  int cmp(int u, int v) const {
    return (u == n) ? ((v == n) ? 0 : -1) : (v == n) ? +1 : (ts[u] < ts[v]) ? -1 : (ts[u] > ts[v]) ? +1 : 0;
  }
  void print() const {
    import std.math : log10;
    import std.stdio : writefln;
    const numDigits = cast(int)(log10(n)) + 1;
    foreach (i; 0 .. n + 1) {
      writefln("%*d %s", numDigits, us[i], ts[us[i] .. $]);
    }
  }
}

unittest {
  /*
    11
    10 a
     7 abra
     0 abracadabra
     3 acadabra
     5 adabra
     8 bra
     1 bracadabra
     4 cadabra
     6 dabra
     9 ra
     2 racadabra
  */
  auto sa = new SuffixArray!(immutable(char))("abracadabra");
  sa.print();
  foreach (i; 0 .. sa.n + 1) {
    assert(sa.su[sa.us[i]] == i);
  }
  foreach (u; 0 .. sa.n + 1) {
    assert(sa.us[sa.su[u]] == u);
  }
  assert(sa.us == [11, 10, 7, 0, 3, 5, 8, 1, 4, 6, 9, 2]);
  assert(sa.lcp == [0, 1, 4, 1, 1, 0, 3, 0, 0, 0, 2]);
}

void main() {
}
