// dmd -O -unittest fft ../number/mod_inv
import modint, mod_inv;

// M: prime, G: primitive root
class Fft(int M_, int G, int K) {
  import std.algorithm : reverse;
  import std.traits : isIntegral;
  alias M = M_;
  // 1, 1/4, 1/8, 3/8, 1/16, 5/16, 3/16, 7/16, ...
  int[] gs;
  this() {
    static assert(2 <= K && K <= 30, "Fft: 2 <= K <= 30 must hold");
    static assert(!((M - 1) & ((1 << K) - 1)), "Fft: 2^K | M - 1 must hold");
    gs = new int[1 << (K - 1)];
    gs[0] = 1;
    long g2 = G, gg = 1;
    for (int e = (M - 1) >> K; e; e >>= 1) {
      if (e & 1) gg = (gg * g2) % M;
      g2 = (g2 * g2) % M;
    }
    gs[1 << (K - 2)] = cast(int)(gg);
    for (int l = 1 << (K - 2); l >= 2; l >>= 1) {
      gs[l >> 1] = cast(int)((cast(long)(gs[l]) * gs[l]) % M);
    }
    assert((cast(long)(gs[1]) * gs[1]) % M == M - 1);
    for (int l = 2; l <= 1 << (K - 2); l <<= 1) {
      foreach (i; 1 .. l) {
        gs[l + i] = cast(int)((cast(long)(gs[l]) * gs[i]) % M);
      }
    }
  }
  void fft(int[] xs) const {
    const n = cast(int)(xs.length);
    assert(!(n & (n - 1)), "Fft.fft: |xs| must be a power of two");
    assert(n <= 1 << K, "Fft.fft: |xs| <= 2^K must hold");
    for (int l = n; l >>= 1; ) {
      foreach (i; 0 .. (n >> 1) / l) {
        const(long) g = gs[i];
        foreach (j; (i << 1) * l .. (i << 1 | 1) * l) {
          const t = cast(int)((g * xs[j + l]) % M);
          if ((xs[j + l] = xs[j] - t) < 0) xs[j + l] += M;
          if ((xs[j] += t) >= M) xs[j] -= M;
        }
      }
    }
  }
  void invFft(int[] xs) const {
    const n = cast(int)(xs.length);
    assert(!(n & (n - 1)), "Fft.invFft: |xs| must be a power of two");
    assert(n <= 1 << K, "Fft.invFft: |xs| <= 2^K must hold");
    for (int l = 1; l < n; l <<= 1) xs[l .. l << 1].reverse;
    for (int l = 1; l < n; l <<= 1) {
      foreach (i; 0 .. (n >> 1) / l) {
        const(long) g = gs[i];
        foreach (j; (i << 1) * l .. (i << 1 | 1) * l) {
          int t = cast(int)((g * (xs[j] - xs[j + l])) % M);
          if (t < 0) t += M;
          if ((xs[j] += xs[j + l]) >= M) xs[j] -= M;
          xs[j + l] = t;
        }
      }
    }
  }
  T[] convolute(T)(inout(T)[] as, inout(T)[] bs) const if (isIntegral!T) {
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
    invFft(xs);
    auto cs = new T[na + nb - 1];
    foreach (i; 0 .. na + nb - 1) cs[i] = cast(T)(xs[i]);
    return cs;
  }
  ModInt!M[] convolute(inout(ModInt!M)[] as, inout(ModInt!M)[] bs) const {
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
    invFft(xs);
    auto cs = new ModInt!M[na + nb - 1];
    foreach (i; 0 .. na + nb - 1) cs[i].x = xs[i];
    return cs;
  }
  int[] convolute(int M1)(inout(ModInt!M1)[] as, inout(ModInt!M1)[] bs) const
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
    invFft(xs);
    return xs[0 .. na + nb - 1];
  }
}

alias Fft0 = Fft!(998244353, 3, 20);


// Fft3_0.M Fft3_1.M Fft3_2.M > 1.15 * 10^27, > 2^89.9
//*
enum FFT_K = 20;
alias Fft3_0 = Fft!(1045430273, 3, FFT_K);  // 2^20 997 + 1
alias Fft3_1 = Fft!(1051721729, 6, FFT_K);  // 2^20 1003 + 1
alias Fft3_2 = Fft!(1053818881, 7, FFT_K);  // 2^20 1005 + 1
//*/
// Fft3_0.M Fft3_1.M Fft3_2.M > 5.95 * 10^25, > 2^85.6
/*
enum FFT_K = 24;
alias Fft3_0 = Fft!(167772161, 3, FFT_K);  // 2^25 5 + 1
alias Fft3_1 = Fft!(469762049, 3, FFT_K);  // 2^26 7 + 1
alias Fft3_2 = Fft!(754974721, 11, FFT_K);  // 2^24 45 + 1
//*/
enum long FFT_INV01 = modInv(Fft3_0.M, Fft3_1.M);
enum long FFT_INV012 = modInv(cast(long)(Fft3_0.M) * Fft3_1.M, Fft3_2.M);
Fft3_0 FFT3_0;
Fft3_1 FFT3_1;
Fft3_2 FFT3_2;
void initFft3() {
  FFT3_0 = new Fft3_0;
  FFT3_1 = new Fft3_1;
  FFT3_2 = new Fft3_2;
}
long[] convolute(inout(long)[] as, inout(long)[] bs) {
  const cs0 = FFT3_0.convolute(as, bs);
  const cs1 = FFT3_1.convolute(as, bs);
  const cs2 = FFT3_2.convolute(as, bs);
  auto cs = new long[cs0.length];
  foreach (i; 0 .. cs0.length) {
    long d0 = cs0[i] % Fft3_0.M;
    long d1 = (FFT_INV01 * (cs1[i] - d0)) % Fft3_1.M;
    if (d1 < 0) d1 += Fft3_1.M;
    long d2 =
        (FFT_INV012 * ((cs2[i] - d0 - Fft3_0.M * d1) % Fft3_2.M)) % Fft3_2.M;
    if (d2 < 0) d2 += Fft3_2.M;
    cs[i] = d0 + Fft3_0.M * d1 + (cast(long)(Fft3_0.M) * Fft3_1.M) * d2;
  }
  return cs;
}
long[] convolute(inout(long)[] as, inout(long)[] bs, long m) {
  const cs0 = FFT3_0.convolute(as, bs);
  const cs1 = FFT3_1.convolute(as, bs);
  const cs2 = FFT3_2.convolute(as, bs);
  auto cs = new long[cs0.length];
  foreach (i; 0 .. cs0.length) {
    long d0 = cs0[i] % Fft3_0.M;
    long d1 = (FFT_INV01 * (cs1[i] - d0)) % Fft3_1.M;
    if (d1 < 0) d1 += Fft3_1.M;
    long d2 =
        (FFT_INV012 * ((cs2[i] - d0 - Fft3_0.M * d1) % Fft3_2.M)) % Fft3_2.M;
    if (d2 < 0) d2 += Fft3_2.M;
    cs[i] =
        (d0 + Fft3_0.M * d1 + ((cast(long)(Fft3_0.M) * Fft3_1.M) % m) * d2) % m;
  }
  return cs;
}
ModInt!M[] convolute(int M)(inout(ModInt!M)[] as, inout(ModInt!M)[] bs) {
  const cs0 = FFT3_0.convolute(as, bs);
  const cs1 = FFT3_1.convolute(as, bs);
  const cs2 = FFT3_2.convolute(as, bs);
  auto cs = new ModInt!M[cs0.length];
  foreach (i; 0 .. cs0.length) {
    long d0 = cs0[i] % Fft3_0.M;
    long d1 = (FFT_INV01 * (cs1[i] - d0)) % Fft3_1.M;
    if (d1 < 0) d1 += Fft3_1.M;
    long d2 =
        (FFT_INV012 * ((cs2[i] - d0 - Fft3_0.M * d1) % Fft3_2.M)) % Fft3_2.M;
    if (d2 < 0) d2 += Fft3_2.M;
    cs[i] =
        (d0 + Fft3_0.M * d1 + ((cast(long)(Fft3_0.M) * Fft3_1.M) % M) * d2) % M;
  }
  return cs;
}


unittest {
  const fft = new Fft!(97, 92, 5);
  int[] as = [31, 41, 59, 26, 53];
  const(int)[] bs = [58, 9, 79, 32, 38, 46];
  const cs = [52, 38, 32, 62, 80, 31, 29, 63, 9, 13];
  assert(fft.convolute(as, bs) == cs);
}

unittest {
  enum MO = 998244353;
  alias Mint = ModInt!MO;
  auto fft = new Fft0;
  auto as = [Mint(1), Mint(1)];
  auto bs = [Mint(-1), Mint(-1), Mint(-1)];
  assert(fft.convolute(as, bs) == [Mint(-1), Mint(-2), Mint(-2), Mint(-1)]);
}

unittest {
  initFft3;
  enum as = [1 * 10L^^10, 2 * 10L^^10, 3 * 10L^^10];
  enum bs = [4 * 10L^^7, 5 * 10L^^7, 6 * 10L^^7, 7 * 10L^^7];
  enum cs = [4 * 10L^^17, 13 * 10L^^17, 28 * 10L^^17, 34 * 10L^^17,
             32 * 10L^^17, 21 * 10L^^17];
  assert(convolute(as, bs) == cs);
  enum m = 1_234_567_890_123L;
  const res = convolute(as, bs, m);
  assert(res.length == 6);
  foreach (i; 0 .. 6) {
    assert(res[i] == cs[i] % m);
  }
}

unittest {
  initFft3;
  enum MO = 10^^9 + 7;
  alias Mint = ModInt!MO;
  auto as = [Mint(1), Mint(1)];
  auto bs = [Mint(-1), Mint(-1), Mint(-1)];
  assert(convolute(as, bs) == [Mint(-1), Mint(-2), Mint(-2), Mint(-1)]);
}

void main() {}
