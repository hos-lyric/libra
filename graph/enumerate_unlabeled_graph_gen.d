// https://users.cecs.anu.edu.au/~bdm/data/graphs.html
//   Characters used are '?'-'~' (ASCII 63-126).
//   Each line contains a graph.
//   First character for n.
//   Following are the lower triangular adjacent matrix:
//     - Pad on the right with 0 so that 6 | length.
//     - Encode each 6 bits in big endian.

// Canonize as minimum adjacent matrix and sort in increasing order.
// Encode using '?'-'~' (ASCII 63-126), in little endian.
import std.algorithm, std.conv, std.format, std.range, std.stdio;
void main() {
  foreach (n; 2 .. 9 + 1) {
    auto file = File(format("bdm/graph%s.g6", n), "r");
    string[] data;
    foreach (line; file.byLine) data ~= line.to!string;
    stderr.writefln("n = %s, |data| = %s", n, data.length);
    stderr.flush;
    string[] canos;
    foreach (index, line; data) {
      if (!(index & (index - 1))) {
        stderr.writefln("index = %s ...", index);
        stderr.flush;
      }
      auto adj = new bool[][](n, n);
      {
        int pos;
        foreach (u; 0 .. n) foreach (v; 0 .. u) {
          if ((line[1 + pos / 6] - 63) >> (6 - 1 - pos % 6) & 1) {
            adj[u][v] = adj[v][u] = true;
          }
          ++pos;
        }
      }
      auto perm = iota(n).array;
      auto best = perm.dup;
      do {
        bool improves() {
          foreach (u; 0 .. n) foreach (v; u + 1 .. n) {
            if (!adj[best[u]][best[v]] && adj[perm[u]][perm[v]]) return false;
            if (adj[best[u]][best[v]] && !adj[perm[u]][perm[v]]) return true;
          }
          return true;
        }
        if (improves()) {
          best = perm.dup;
        }
      } while (perm.nextPermutation);
      string cano;
      foreach (u; 0 .. n) foreach (v; u + 1 .. n) {
        cano ~= adj[best[u]][best[v]] ? '1' : '0';
      }
      canos ~= cano;
    }
    canos.sort;
    foreach (i; 0 .. cast(int)(canos.length) - 1) {
      assert(canos[i] < canos[i + 1]);
    }
    write("\"");
    foreach (cano; canos) {
      const len = (n * (n - 1) / 2 + 6 - 1) / 6;
      auto keys = new int[len];
      foreach (i; 0 .. n * (n - 1) / 2) if (cano[i] == '1') {
        keys[i / 6] |= 1 << (i % 6);
      }
      foreach (key; keys) {
        const c = cast(char)('?' + key);
        if (c == '\\') write("\\");
        write(c);
      }
    }
    writeln("\",");
  }
}
