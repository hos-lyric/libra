// dmd -I=../number -O -unittest fft
import modint;

// M: prime, G: primitive root
class Fft(int M, int G, int K) {
  import std.algorithm : reverse, swap;
  // 1, 1/4, 1/8, 3/8, 1/16, 5/16, 3/16, 7/16, ...
  int[] g;
  this() {
    static assert(K >= 2, "Fft: K >= 2 must hold");
    static assert(!((M - 1) & ((1 << K) - 1)), "Fft: 2^K | M - 1 must hold");
    g = new int[1 << (K - 1)];
    g[0] = 1;
    long g2 = G, gg = 1;
    for (int e = (M - 1) >> K; e; e >>= 1) {
      if (e & 1) gg = (gg * g2) % M;
      g2 = (g2 * g2) % M;
    }
    g[1 << (K - 2)] = cast(int)(gg);
    for (int l = 1 << (K - 2); l >= 2; l >>= 1) {
      g[l >> 1] = cast(int)((cast(long)(g[l]) * g[l]) % M);
    }
    assert((cast(long)(g[1]) * g[1]) % M == M - 1);
    for (int l = 2; l <= 1 << (K - 2); l <<= 1) {
      foreach (i; 1 .. l) {
        g[l + i] = cast(int)((cast(long)(g[l]) * g[i]) % M);
      }
    }
  }
  void fft(int[] xs) const {
    const n = cast(int)(xs.length);
    assert(!(n & (n - 1)), "Fft.fft: |xs| must be a power of two");
    assert(n <= 1 << K, "Fft.fft: |xs| <= 2^K must hold");
    for (int l = n; l >>= 1; ) {
      foreach (i; 0 .. (n >> 1) / l) {
        foreach (j; (i << 1) * l .. (i << 1 | 1) * l) {
          const t = cast(int)((cast(long)(g[i]) * xs[j + l]) % M);
          if ((xs[j + l] = xs[j] - t) < 0) xs[j + l] += M;
          if ((xs[j] += t) >= M) xs[j] -= M;
        }
      }
    }
    for (int i = 0, j = 0; i < n; ++i) {
      if (i < j) swap(xs[i], xs[j]);
      for (int l = n; (l >>= 1) && !((j ^= l) & l); ) {}
    }
  }
  int[] convolution(inout(int)[] as, inout(int)[] bs) const {
    const na = cast(int)(as.length), nb = cast(int)(bs.length);
    int n, invN = 1;
    for (n = 1; n < na + nb - 1; n <<= 1) {
      invN = ((invN & 1) ? (invN + M) : invN) >> 1;
    }
    auto xs = new int[n], ys = new int[n];
    xs[0 .. na] = as[];
    ys[0 .. nb] = bs[];
    fft(xs);
    fft(ys);
    foreach (i; 0 .. n) {
      xs[i] = cast(int)((((cast(long)(xs[i]) * ys[i]) % M) * invN) % M);
    }
    xs[1 .. n].reverse;
    fft(xs);
    return xs[0 .. na + nb - 1];
  }
  ModInt!M[] convolution(inout(ModInt!M)[] as, inout(ModInt!M)[] bs) const {
    const na = cast(int)(as.length), nb = cast(int)(bs.length);
    int n, invN = 1;
    for (n = 1; n < na + nb - 1; n <<= 1) {
      invN = ((invN & 1) ? (invN + M) : invN) >> 1;
    }
    auto xs = new int[n], ys = new int[n];
    foreach (i; 0 .. na) xs[i] = as[i].x;
    foreach (i; 0 .. nb) ys[i] = bs[i].x;
    fft(xs);
    fft(ys);
    foreach (i; 0 .. n) {
      xs[i] = cast(int)((((cast(long)(xs[i]) * ys[i]) % M) * invN) % M);
    }
    xs[1 .. n].reverse;
    fft(xs);
    auto cs = new ModInt!M[na + nb - 1];
    foreach (i; 0 .. na + nb - 1) cs[i].x = xs[i];
    return cs;
  }
}

unittest {
  const fft = new Fft!(97, 92, 5);
  int[] as = [31, 41, 59, 26, 53];
  const(int)[] bs = [58, 9, 79, 32, 38, 46];
  const cs = [52, 38, 32, 62, 80, 31, 29, 63, 9, 13];
  assert(fft.convolution(as, bs) == cs);
}

unittest {
  enum MO = 998244353;
  alias Mint = ModInt!MO;
  auto fft = new Fft!(MO, 3, 20);
  auto as = [Mint(1), Mint(1)];
  auto bs = [Mint(-1), Mint(-1), Mint(-1)];
  assert(fft.convolution(as, bs) == [Mint(-1), Mint(-2), Mint(-2), Mint(-1)]);
}

void main() {
}
