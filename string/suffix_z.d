// zs[i] := lcp(as[0, n), as[i, n))
// 0    i-j     j     i
// |-------|    |-------|    zs[j]
// |---| |---|  |---| |---|  zs[i-j]
int[] suffixZ(T)(const(T[]) as) {
  import std.algorithm : max;
  const n = cast(int)(as.length);
  if (n == 0) return [];
  auto zs = new int[n];
  int j;
  foreach (i; 1 .. n) {
    if (i + zs[i - j] < j + zs[j]) {
      zs[i] = zs[i - j];
    } else {
      int z = max(j + zs[j] - i, 0);
      for (; i + z < n && as[z] == as[i + z]; ++z) {}
      zs[i] = z;
      j = i;
    }
  }
  zs[0] = n;
  return zs;
}

////////////////////////////////////////////////////////////////////////////////

unittest {
  assert(suffixZ([0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0]) ==
         [12, 1, 0, 5, 1, 0, 2, 1, 0, 2, 2, 1]);
  assert(suffixZ([-1, -1]) == [2, 1]);
  assert(suffixZ("") == []);
  assert(suffixZ("abracadabra") == [11, 0, 0, 1, 0, 1, 0, 4, 0, 0, 1]);
}

void main() {
}
