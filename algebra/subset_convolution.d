T[] subsetConvolution(T)(T[] as, T[] bs)
in {
  assert(as.length == bs.length, "subsetConvolution: |as| = |bs| must hold");
  assert(as.length && !(as.length & as.length - 1),
         "subsetConvolution: |as| and |bs| must be a power of two");
}
do {
  import core.bitop : bsr, popcnt;
  const n = bsr(as.length);
  auto fas = new T[][](n + 1, 1 << n);
  foreach (h; 0 .. 1 << n) fas[popcnt(h)][h] += as[h];
  foreach (i; 0 .. n + 1) foreach (j; 0 .. n) foreach (h; 0 .. 1 << n) {
    if (!(h & 1 << j)) fas[i][h | 1 << j] += fas[i][h];
  }
  auto fbs = new T[][](n + 1, 1 << n);
  foreach (h; 0 .. 1 << n) fbs[popcnt(h)][h] += bs[h];
  foreach (i; 0 .. n + 1) foreach (j; 0 .. n) foreach (h; 0 .. 1 << n) {
    if (!(h & 1 << j)) fbs[i][h | 1 << j] += fbs[i][h];
  }
  auto fcs = new T[][](n + 1, 1 << n);
  foreach (i; 0 .. n + 1) foreach (j; 0 .. n - i + 1) foreach (h; 0 .. 1 << n) {
    fcs[i + j][h] += fas[i][h] * fbs[j][h];
  }
  foreach (i; 0 .. n + 1) foreach (j; 0 .. n) foreach (h; 0 .. 1 << n) {
    if (!(h & 1 << j)) fcs[i][h | 1 << j] -= fcs[i][h];
  }
  auto cs = new T[1 << n];
  foreach (h; 0 .. 1 << n) cs[h] = fcs[popcnt(h)][h];
  return cs;
}

unittest {
  assert(subsetConvolution([5], [8]) == [40]);
  assert(subsetConvolution([1, 2, 3, 4, 5, 6, 7, 8],
                           [9, 10, 11, 12, 13, 14, 15, 16]) ==
         [9, 28, 38, 100, 58, 144, 172, 408]);
}

void main() {
}
