import modint;

enum MO = 998244353;
alias Mint = ModInt!MO;

// inv[i] = 1 / i, fac[i] = i!, invFac[i] = 1 / i!
Mint[] inv, fac, invFac;
void prepareFac(int lim) {
  inv = new Mint[lim];
  fac = new Mint[lim];
  invFac = new Mint[lim];
  inv[1] = 1;
  foreach (i; 2 .. lim) {
    inv[i] = -(Mint.M / i) * inv[cast(size_t)(Mint.M % i)];
  }
  fac[0] = invFac[0] = 1;
  foreach (i; 1 .. lim) {
    fac[i] = fac[i - 1] * i;
    invFac[i] = invFac[i - 1] * inv[i];
  }
}

// Find f(n) for the polynomial f s.t. fs = [f(0), f(1), ...] and deg f < |fs|
Mint interpolateIota(const(Mint[]) fs, long n) {
  const fsLen = cast(int)(fs.length);
  auto prodR = new Mint[fsLen + 1];
  prodR[fsLen] = 1;
  foreach_reverse (i; 0 .. fsLen) prodR[i] = (n - i) * prodR[i + 1];
  Mint ans;
  Mint prodL = 1;
  for (int i = 0; i < fsLen; ++i) {
    // (i - 0) ... (i - (i - 1)) (i - (i + 1)) ... (i - (fsLen - 1))
    ans += invFac[i] * (((fsLen - 1 - i) & 1) ? -1 : +1) *
           invFac[fsLen - 1 - i] * fs[i] * prodL * prodR[i + 1];
    prodL *= (n - i);
  }
  return ans;
}

// pws[i] = i^d (0 <= i < n)
Mint[] getMonomials(long d, int n) {
  auto lpf = new int[n];
  foreach (i; 0 .. n) lpf[i] = i;
  foreach (p; 2 .. n) if (lpf[p] == p) {
    for (int i = 2 * p; i < n; i += p) if (lpf[i] > p) lpf[i] = p;
  }
  auto pws = new Mint[n];
  foreach (i; 0 .. n) {
    pws[i] = (lpf[i] == i) ? Mint(i)^^d : (pws[lpf[i]] * pws[i / lpf[i]]);
  }
  return pws;
}

// \sum_{i=0}^{\infty} r^i f(i) (deg f <= d)
Mint sumPowerPolyLimit(Mint r, int d, const(Mint[]) fs) {
  assert(r.x != 1, "sumPowerPolyLimit: r != 1 must hold");
  assert(d + 1 < inv.length, "sumPowerPolyLimit: inv[d + 1] must be prepared");
  assert(d + 1 <= fs.length, "sumPowerPolyLimit: d + 1 < |fs| must hold");
  auto rr = new Mint[d + 1];
  rr[0] = 1;
  foreach (i; 1 .. d + 1) rr[i] = rr[i - 1] * r;
  Mint ans, sumRF;
  foreach (i; 0 .. d + 1) {
    sumRF += rr[i] * fs[i];
    ans += invFac[d - i] * invFac[i + 1] * (((d - i) & 1) ? -1 : +1) *
           rr[d - i] * sumRF;
  }
  ans *= (1 - r)^^(-(d + 1)) * fac[d + 1];
  return ans;
}

// \sum_{i=0}^{\infty} r^i i^d
Mint sumPowerPolyLimit(Mint r, int d) {
  return sumPowerPolyLimit(r, d, getMonomials(d, d + 1));
}

// \sum_{i=0}^{n-1} r^i f(i) (deg f <= d)
Mint sumPowerPoly(Mint r, int d, const(Mint[]) fs, long n) {
  assert(d + 1 < inv.length, "sumPowerPoly: inv[d + 1] must be prepared");
  assert(d + 1 <= fs.length, "sumPowerPoly: d + 1 < |fs| must hold");
  assert(n >= 0, "sumPowerPoly: n >= 0 must hold.");
  if (r.x == 0) return (0 < n) ? fs[0] : Mint(0);
  auto gs = new Mint[d + 2];
  Mint rr = 1;
  gs[0] = 0;
  foreach (i; 0 .. d + 1) {
    gs[i + 1] = gs[i] + rr * fs[i];
    rr *= r;
  }
  if (r.x == 1) return interpolateIota(gs, n);
  const c = sumPowerPolyLimit(r, d, fs);
  const rInv = r.inv();
  Mint rrInv = 1;
  foreach (i; 0 .. d + 2) {
    gs[i] = rrInv * (gs[i] - c);
    rrInv *= rInv;
  }
  return c + r^^n * interpolateIota(gs, n);
}

// \sum_{i=0}^{n-1} r^i i^d
Mint sumPowerPoly(Mint r, int d, long n) {
  return sumPowerPoly(r, d, getMonomials(d, d + 1), n);
}


// prepareFac
unittest {
  enum lim = 200;
  prepareFac(lim);
  foreach (i; 1 .. lim) {
    assert((inv[i] * i).x == 1);
  }
  assert(fac[20].x == 401576539);
  assert(invFac[20].x == 400962745);
}

// interpolateIota
unittest {
  // 0
  assert(interpolateIota([Mint(0)], 0).x == 0);
  // i^2
  assert(interpolateIota([Mint(0), Mint(1), Mint(4)], 10).x == 100);
  // i^3 - i + 3
  assert(interpolateIota([Mint(3), Mint(3), Mint(9), Mint(27), Mint(63)], -10)
             .x == MO - 987);
}

// getMonimials
unittest {
  enum d = 58;
  enum n = 100;
  const pws = getMonomials(d, n);
  foreach (i; 0 .. n) {
    Mint pw = 1;
    foreach (_; 0 .. d) {
      pw *= i;
    }
    assert(pw.x == pws[i].x);
  }
}

// sumPowerPolyLimit
unittest {
  // (1/2)^i i^5
  assert(sumPowerPolyLimit(inv[2], 5).x == 1082);
  // (-1/3)^i (i^3 - i + 3)
  assert(sumPowerPolyLimit(-inv[3], 4,
                           [Mint(3), Mint(3), Mint(9), Mint(27), Mint(63)]).x ==
             (Mint(315) * inv[128]).x);
}

// sumPowerPoly
unittest {
  // 2^i i^5
  assert(sumPowerPoly(Mint(2), 5, 8).x == 2767418);
  // 3^i (i^3 - i + 3)
  assert(sumPowerPoly(Mint(3), 4,
                      [Mint(3), Mint(3), Mint(9), Mint(27), Mint(63)], 15).x ==
             813522614);
}

void main() {}
