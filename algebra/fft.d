// dmd -O -unittest fft ../number/modint.d ../number/mod_inv.d
import modint, mod_inv;

// M: prime, G: primitive root
class Fft(int M_, int G, int K) {
  import std.algorithm : reverse, swap;
  import std.traits : isIntegral;
  alias M = M_;
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
  T[] convolution(T)(inout(T)[] as, inout(T)[] bs) const if (isIntegral!T) {
    const na = cast(int)(as.length), nb = cast(int)(bs.length);
    int n, invN = 1;
    for (n = 1; n < na + nb - 1; n <<= 1) {
      invN = ((invN & 1) ? (invN + M) : invN) >> 1;
    }
    auto xs = new int[n], ys = new int[n];
    foreach (i; 0 .. na) if ((xs[i] = cast(int)(as[i] % M)) < 0) xs[i] += M;
    foreach (i; 0 .. nb) if ((ys[i] = cast(int)(bs[i] % M)) < 0) ys[i] += M;
    fft(xs);
    fft(ys);
    foreach (i; 0 .. n) {
      xs[i] = cast(int)((((cast(long)(xs[i]) * ys[i]) % M) * invN) % M);
    }
    xs[1 .. n].reverse;
    fft(xs);
    auto cs = new T[na + nb - 1];
    foreach (i; 0 .. na + nb - 1) cs[i] = cast(T)(xs[i]);
    return cs;
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
  int[] convolution(int M1)(inout(ModInt!M1)[] as, inout(ModInt!M1)[] bs) const
      if (M != M1) {
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
    return xs[0 .. na + nb - 1];
  }
}

enum FFT_K = 20;
alias Fft0 = Fft!(1045430273, 3, FFT_K);  // 2^20 997 + 1
alias Fft1 = Fft!(1051721729, 6, FFT_K);  // 2^20 1003 + 1
alias Fft2 = Fft!(1053818881, 7, FFT_K);  // 2^20 1005 + 1
// Fft0.M Fft1.M Fft2.M > 5.95 * 10^25 > 2^85.6
// enum FFT_K = 24;
// alias Fft0 = Fft!(167772161, 3, FFT_K);  // 2^25 5 + 1
// alias Fft1 = Fft!(469762049, 3, FFT_K);  // 2^26 7 + 1
// alias Fft2 = Fft!(754974721, 11, FFT_K);  // 2^24 45 + 1
enum long FFT_INV01 = modInv(Fft0.M, Fft1.M);
enum long FFT_INV012 = modInv(cast(long)(Fft0.M) * Fft1.M, Fft2.M);
Fft0 FFT0;
Fft1 FFT1;
Fft2 FFT2;
void fftInit() {
  FFT0 = new Fft0;
  FFT1 = new Fft1;
  FFT2 = new Fft2;
}
long[] convolution(inout(long)[] as, inout(long)[] bs) {
  const cs0 = FFT0.convolution(as, bs);
  const cs1 = FFT1.convolution(as, bs);
  const cs2 = FFT2.convolution(as, bs);
  auto cs = new long[cs0.length];
  foreach (i; 0 .. cs0.length) {
    long d0 = cs0[i] % Fft0.M;
    long d1 = (FFT_INV01 * (cs1[i] - d0)) % Fft1.M;
    if (d1 < 0) d1 += Fft1.M;
    long d2 = (FFT_INV012 * ((cs2[i] - d0 - Fft0.M * d1) % Fft2.M)) % Fft2.M;
    if (d2 < 0) d2 += Fft2.M;
    cs[i] = d0 + Fft0.M * d1 + (cast(long)(Fft0.M) * Fft1.M) * d2;
  }
  return cs;
}
long[] convolution(inout(long)[] as, inout(long)[] bs, long m) {
  const cs0 = FFT0.convolution(as, bs);
  const cs1 = FFT1.convolution(as, bs);
  const cs2 = FFT2.convolution(as, bs);
  auto cs = new long[cs0.length];
  foreach (i; 0 .. cs0.length) {
    long d0 = cs0[i] % Fft0.M;
    long d1 = (FFT_INV01 * (cs1[i] - d0)) % Fft1.M;
    if (d1 < 0) d1 += Fft1.M;
    long d2 = (FFT_INV012 * ((cs2[i] - d0 - Fft0.M * d1) % Fft2.M)) % Fft2.M;
    if (d2 < 0) d2 += Fft2.M;
    cs[i] = (d0 + Fft0.M * d1 + ((cast(long)(Fft0.M) * Fft1.M) % m) * d2) % m;
  }
  return cs;
}
ModInt!M[] convolution(int M)(inout(ModInt!M)[] as, inout(ModInt!M)[] bs) {
  auto asInt = new int[as.length], bsInt = new int[bs.length];
  const cs0 = FFT0.convolution(as, bs);
  const cs1 = FFT1.convolution(as, bs);
  const cs2 = FFT2.convolution(as, bs);
  auto cs = new ModInt!M[cs0.length];
  foreach (i; 0 .. cs0.length) {
    long d0 = cs0[i] % Fft0.M;
    long d1 = (FFT_INV01 * (cs1[i] - d0)) % Fft1.M;
    if (d1 < 0) d1 += Fft1.M;
    long d2 = (FFT_INV012 * ((cs2[i] - d0 - Fft0.M * d1) % Fft2.M)) % Fft2.M;
    if (d2 < 0) d2 += Fft2.M;
    cs[i] = (d0 + Fft0.M * d1 + ((cast(long)(Fft0.M) * Fft1.M) % M) * d2) % M;
  }
  return cs;
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

unittest {
  fftInit;
  enum as = [1 * 10L^^10, 2 * 10L^^10, 3 * 10L^^10];
  enum bs = [4 * 10L^^7, 5 * 10L^^7, 6 * 10L^^7, 7 * 10L^^7];
  enum cs = [4 * 10L^^17, 13 * 10L^^17, 28 * 10L^^17, 34 * 10L^^17,
             32 * 10L^^17, 21 * 10L^^17];
  assert(convolution(as, bs) == cs);
  enum m = 1_234_567_890_123L;
  const res = convolution(as, bs, m);
  assert(res.length == 6);
  foreach (i; 0 .. 6) {
    assert(res[i] == cs[i] % m);
  }
}

unittest {
  enum MO = 10^^9 + 7;
  alias Mint = ModInt!MO;
  auto as = [Mint(1), Mint(1)];
  auto bs = [Mint(-1), Mint(-1), Mint(-1)];
  assert(convolution(as, bs) == [Mint(-1), Mint(-2), Mint(-2), Mint(-1)]);
}

void main() {
}
