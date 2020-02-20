// a^-1 (mod 2^64)
long modInv(long a)
in {
  assert(a & 1, "modInv: a must be odd");
}
do {
  long b = ((a << 1) + a) ^ 2;
  b *= 2 - a * b;
  b *= 2 - a * b;
  b *= 2 - a * b;
  b *= 2 - a * b;
  return b;
}

// a^-1 (mod m)
long modInv(long a, long m)
in {
  assert(m > 0, "modInv: m > 0 must hold");
}
do {
  long b = m, x = 1, y = 0, t;
  for (; ; ) {
    t = a / b; a -= t * b;
    if (a == 0) {
      assert(b == 1 || b == -1, "modInv: gcd(a, m) != 1");
      if (b == -1) y = -y;
      return (y < 0) ? (y + m) : y;
    }
    x -= t * y;
    t = b / a; b -= t * a;
    if (b == 0) {
      assert(a == 1 || a == -1, "modInv: gcd(a, m) != 1");
      if (a == -1) x = -x;
      return (x < 0) ? (x + m) : x;
    }
    y -= t * x;
  }
}

// 2^-31 a (mod M)
long montgomery(long M)(long a) if (1 <= M && M <= 0x7fffffff && (M & 1))
in {
  assert(0 <= a && a < (M << 31), "montgomery: 0 <= a < 2^31 M must hold");
}
do {
  enum negInvM = -modInv(M) & 0x7fffffff;
  const b = (a + ((a * negInvM) & 0x7fffffff) * M) >> 31;
  return (b >= M) ? (b - M) : b;
}

// FFT on Z / M Z with Montgomery multiplication (x -> 2^31 x)
//   G: primitive 2^K-th root of unity
class FFT(long M, int K, long G)
    if (is(typeof(montgomery!(M)(0))) && K >= 0 && 0 < G && G < M) {
  import std.algorithm : swap;
  import core.bitop : bsf;

  int n, invN;
  long[] g;

  this(int n)
  in {
    assert(!(n & (n - 1)), "FFT.this: n must be a power of 2");
    assert(4 <= n && n <= 1 << K, "FFT.this: 4 <= n <= 2^K must hold");
  }
  do {
    this.n = n;
    this.invN = ((1L << 31) / n) % M;
    g.length = n + 1;
    g[0] = (1L << 31) % M;
    g[1] = (G << 31) % M;
    foreach (_; 0 .. K - bsf(n)) {
      g[1] = montgomery!(M)(g[1] * g[1]);
    }
    foreach (i; 2 .. n + 1) {
      g[i] = montgomery!(M)(g[i - 1] * g[1]);
    }
    assert(g[0] != g[n >> 1] && g[0] == g[n],
           "FFT.this: G must be a primitive 2^K-th root of unity");
    for (int i = 0, j = 0; i < n >> 1; ++i) {
      if (i < j) {
        swap(g[i], g[j]);
        swap(g[n - i], g[n - j]);
      }
      for (int m = n >> 1; (m >>= 1) && !((j ^= m) & m); ) {}
    }
  }

  void fftMontgomery(long[] x, bool inv)
  in {
    assert(x.length == n, "FFT.fftMontgomery: |x| = n must hold");
  }
  do {
    foreach_reverse (h; 0 .. bsf(n)) {
      const l = 1 << h;
      foreach (i; 0 .. n >> 1 >> h) {
        const gI = g[inv ? (n - i) : i];
        foreach (j; i << 1 << h .. ((i << 1) + 1) << h) {
          const t = montgomery!(M)(gI * x[j + l]);
          if ((x[j + l] = x[j] - t) < 0) {
            x[j + l] += M;
          }
          if ((x[j] += t) >= M) {
            x[j] -= M;
          }
        }
      }
    }
    for (int i = 0, j = 0; i < n; ++i) {
      if (i < j) {
        swap(x[i], x[j]);
      }
      for (int m = n; (m >>= 1) && !((j ^= m) & m); ) {}
    }
    if (inv) {
      foreach (i; 0 .. n) {
        x[i] = montgomery!(M)(invN * x[i]);
      }
    }
  }

  long[] convolution(long[] a, long[] b)
  in {
    assert(a.length <= n, "FFT.convolution: |a| <= n must hold");
    assert(b.length <= n, "FFT.convolution: |b| <= n must hold");
  }
  do {
    auto x = new long[n], y = new long[n];
    foreach (i; 0 .. a.length) {
      const t = a[i] % M;
      x[i] = (((t < 0) ? (t + M) : t) << 31) % M;
    }
    foreach (i; 0 .. b.length) {
      const t = b[i] % M;
      y[i] = (((t < 0) ? (t + M) : t) << 31) % M;
    }
    fftMontgomery(x, false);
    fftMontgomery(y, false);
    foreach (i; 0 .. n) {
      x[i] = montgomery!(M)(x[i] * y[i]);
    }
    fftMontgomery(x, true);
    foreach (i; 0 .. n) {
      x[i] = montgomery!(M)(x[i]);
    }
    return x;
  }
}

// P0 P1 P2 > 2^90, P0 + P1 + P2 = 2^32 + 3
enum FFT_P0 = 2013265921L;  // 2^27 15 + 1
enum FFT_P1 = 1811939329L;  // 2^26 27 + 1
enum FFT_P2 =  469762049L;  // 2^26  7 + 1
alias FFT0 = FFT!(FFT_P0, 27, 440564289L);  // 31^15
alias FFT1 = FFT!(FFT_P1, 26,  72705542L);  // 13^27
alias FFT2 = FFT!(FFT_P2, 26,      2187L);  //  3^ 7

// Convolution of a and b (indices mod fft0.n)
//   modify a and b so that 0 <= a[i] < m, 0 <= b[i] < m
long[] convolution(FFT0 fft0, FFT1 fft1, FFT2 fft2, long[] a, long[] b, long m)
in {
  assert(fft0.n == fft1.n && fft0.n == fft2.n, "convolution: fft0.n = fft1.n = fft2.n must hold");
  assert(1 <= m && m <= 0x7fffffff, "convolution: 1 <= m < 2^31 must hold");
}
do {
  enum FFT_INV01 = modInv(FFT_P0, FFT_P1);
  enum FFT_INV012 = modInv(FFT_P0 * FFT_P1, FFT_P2);
  foreach (i; 0 .. a.length) {
    if ((a[i] %= m) < 0) {
      a[i] += m;
    }
  }
  foreach (i; 0 .. b.length) {
    if ((b[i] %= m) < 0) {
      b[i] += m;
    }
  }
  const x0 = fft0.convolution(a, b);
  const x1 = fft1.convolution(a, b);
  const x2 = fft2.convolution(a, b);
  auto x = new long[fft0.n];
  foreach (i; 0 .. fft0.n) {
    auto y0 = x0[i] % FFT_P0;
    auto y1 = (FFT_INV01 * (x1[i] - y0)) % FFT_P1;
    if (y1 < 0) {
      y1 += FFT_P1;
    }
    auto y2 = (FFT_INV012 * ((x2[i] - y0 - FFT_P0 * y1) % FFT_P2)) % FFT_P2;
    if (y2 < 0) {
      y2 += FFT_P2;
    }
    x[i] = (y0 + FFT_P0 * y1 + ((FFT_P0 * FFT_P1) % m) * y2) % m;
  }
  return x;
}

// X^k mod f(X), coefficients in Z / m Z
//   f: monic (array length: deg f)
long[] polyPower(long k, long[] f, long m)
in {
  assert(k >= 0, "polyPower: k >= 0 must hold");
  assert(f.length >= 1, "polyPower: deg f >= 1 must hold");
  assert(1 <= m && m <= 0x7fffffff, "polyPower: 1 <= m < 2^31 must hold");
}
do {
  import std.algorithm.comparison : min;
  import core.bitop : bsr;
  const n = cast(int)(f.length);
  auto fRev = new long[n + 1];
  fRev[0] = 1;
  foreach (i; 1 .. n + 1) {
    fRev[i] = f[n - i];
  }
  auto negInvFRev = [m - 1];
  for (int l = 1; l < n; l <<= 1) {
    auto fft0 = new FFT0(l << 2), fft1 = new FFT1(l << 2), fft2 = new FFT2(l << 2);
    auto t = convolution(fft0, fft1, fft2, fRev[0 .. min(l << 1, n + 1)], negInvFRev, m)[0 .. l << 1];
    t[0] += 2;
    negInvFRev = convolution(fft0, fft1, fft2, negInvFRev, t, m)[0 .. l << 1];
  }
  auto a = new long[n];
  if ((a[0] = 1) >= m) {
    a[0] -= m;
  }
  if (k > 0) {
    int nn;
    for (nn = 4; nn < 2 * n; nn <<= 1) {}
    auto fft0 = new FFT0(nn), fft1 = new FFT1(nn), fft2 = new FFT2(nn);
    foreach_reverse (h; 0 .. bsr(k) + 1) {
      a = convolution(fft0, fft1, fft2, a, a, m);
      auto aRev = new long[n];
      foreach (i; 0 .. n) {
        aRev[i] = a[2 * n - 1 - i];
      }
      auto negRevQ = convolution(fft0, fft1, fft2, aRev, negInvFRev, m);
      auto negQ = new long[n];
      foreach (i; 0 .. n) {
        negQ[i] = negRevQ[n - 1 - i];
      }
      auto t = convolution(fft0, fft1, fft2, f, negQ, m);
      foreach (i; 0 .. n) {
        if ((a[i] += t[i]) >= m) {
          a[i] -= m;
        }
      }
      a.length = n;
      if ((k >> h) & 1) {
        a = [0L] ~ a;
        foreach (i; 0 .. n) {
          if (((a[i] -= a[n] * f[i]) %= m) < 0) {
            a[i] += m;
          }
        }
        a.length = n;
      }
    }
  }
  return a;
}

// FFT.convolution
unittest {
  enum P = 2013265921L, K = 27, G = 440564289L;
  enum n = 1024;
  auto fft = new FFT!(P, K, G)(n);
  auto a = new long[500];
  auto b = new long[800];
  foreach (i; 0 .. a.length) {
    a[i] = i * i;
  }
  foreach (j; 0 .. b.length) {
    b[j] = j - (31415926535L ^ j);
  }
  auto brute = new long[n];
  foreach (i; 0 .. a.length) foreach (j; 0 .. b.length) {
    (brute[(i + j) % n] += (a[i] % P) * (b[j] % P)) %= P;
  }
  foreach (k; 0 .. n) {
    brute[k] = (brute[k] % P + P) % P;
  }
  auto result = fft.convolution(a, b);
  assert(brute == result);
}

// convolution
unittest {
  enum m = (1L << 31) - 2;
  enum n = 1024;
  auto a = new long[600];
  auto b = new long[900];
  foreach (i; 0 .. a.length) {
    a[i] = i * i * i;
  }
  foreach (j; 0 .. b.length) {
    b[j] = j - (2718281828459045L ^ j);
  }
  auto brute = new long[n];
  foreach (i; 0 .. a.length) foreach (j; 0 .. b.length) {
    (brute[(i + j) % n] += (a[i] % m) * (b[j] % m)) %= m;
  }
  foreach (k; 0 .. n) {
    brute[k] = (brute[k] % m + m) % m;
  }
  auto result = convolution(new FFT0(n), new FFT1(n), new FFT2(n), a, b, m);
  assert(brute == result);
}

// polyPower
unittest {
import std.stdio;
  // X^k mod X^3 - 3 X^2 + 2
  enum m = (1L << 31) - 2;
  enum len = 100;
  auto a = new long[len];
  a[0] = 1 % m;
  a[1] = 2 % m;
  a[2] = 4 % m;
  foreach (i; 3 .. len) {
    if ((a[i] = (3 * a[i - 1] - 2 * a[i - 3]) % m) < 0) {
      a[i] += m;
    }
  }
  foreach (k; 0 .. len) {
    auto result = polyPower(k, [2, 0, -3], m);
    assert(result.length == 3);
    foreach (i; 0 .. 3) {
      assert(0 <= result[i] && result[i] < m);
    }
    long sum;
    foreach (i; 0 .. 3) {
      (sum += result[i] * a[i]) %= m;
    }
    assert(sum == a[k]);
  }
}

void main() {
}
