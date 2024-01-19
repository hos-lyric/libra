// class Func = TX -> TY
//   For any f, g: Func, x -> sgn(g(x) - f(x)) must be monotone on [L, R].
class LiChaoTree(Func) {
  import std.algorithm : swap;
  alias TX = Func.TX;
  alias TY = Func.TY;
  const(TX) L, R;
  class Tree {
    Tree l, r;
    Func f;
    this(Func f) {
      this.f = f;
    }
  }
  Tree root;

  // [L, R)
  this(TX L, TX R) {
    assert(L < R, "LiChaoTree: L < R must hold");
    this.L = L;
    this.R = R;
  }
  // Add g to the whole [L, R)
  void add(Func g) {
    root = add(root, L, R, g);
  }
  // Add g to [a, b)
  void add(TX a, TX b, Func g) {
    root = add(root, L, R, a, b, g);
  }
  // Get max at a
  TY opCall(TX a) {
    TY mx = TY.min;
    TX l = L, r = R;
    for (Tree u = root; u; ) {
      if (u.f) {
        const fX = u.f(a);
        if (mx < fX) mx = fX;
      }
      const mid = l + (r - l) / 2;
      if (a < mid) {
        u = u.l; r = mid;
      } else {
        u = u.r; l = mid;
      }
    }
    return mx;
  }

 private:
  Tree add(Tree u0, TX l, TX r, Func g) {
    if (!u0) return new Tree(g);
    TY gL = g(l), gR = g(r);
    for (Tree u = u0; ; ) {
      TY fL = u.f ? u.f(l) : TY.min, fR = u.f ? u.f(r) : TY.min;
      if (fL >= gL && fR >= gR) return u0;
      if (fL <= gL && fR <= gR) { u.f = g; return u0; }
      if (r - l == 1) { if (fL <= gL) { u.f = g; } return u0; }
      const mid = l + (r - l) / 2;
      TY fMid = u.f(mid), gMid = g(mid);
      if (fMid < gMid) {
        swap(u.f, g);
        if (!g) return u0;
        if (gL < fL) {
          if (!u.l) { u.l = new Tree(g); return u0; }
          u = u.l; r = mid; gL = fL; gR = fMid;
        } else {
          if (!u.r) { u.r = new Tree(g); return u0; }
          u = u.r; l = mid; gL = fMid; gR = fR;
        }
      } else {
        if (fL < gL) {
          if (!u.l) { u.l = new Tree(g); return u0; }
          u = u.l; r = mid; gR = gMid;
        } else {
          if (!u.r) { u.r = new Tree(g); return u0; }
          u = u.r; l = mid; gL = gMid;
        }
      }
    }
  }
  Tree add(Tree u, TX l, TX r, TX a, TX b, Func g) {
    if (b <= l || r <= a) return u;
    if (a <= l && r <= b) return add(u, l, r, g);
    if (u && u.f && u.f(l) >= g(l) && u.f(r) >= g(r)) return u;
    if (!u) u = new Tree(null);
    const mid = l + (r - l) / 2;
    u.l = add(u.l, l, mid, a, b, g);
    u.r = add(u.r, mid, r, a, b, g);
    return u;
  }
}

// y = p x + q
class Line {
  alias TX = long;
  alias TY = long;
  long p, q;
  this(long p, long q) {
    this.p = p;
    this.q = q;
  }
  TY opCall(TX x) {
    return p * x + q;
  }
}

// line
unittest {
  auto lct = new LiChaoTree!Line(-10, 10);
  assert(lct(0) == long.min);
  lct.add(new Line(1, 3));
  assert(lct(0) == 3);
  lct.add(new Line(2, 6));
  assert(lct(-4) == -1);
  assert(lct(-3) == 0);
  assert(lct(-2) == 2);
  lct.add(new Line(1, 4));
  assert(lct(-4) == 0);
  assert(lct(-3) == 1);
  assert(lct(-2) == 2);
  assert(lct(-1) == 4);
  lct.add(new Line(5, 9));
  assert(lct(-4) == 0);
  assert(lct(-3) == 1);
  assert(lct(-2) == 2);
  assert(lct(-1) == 4);
  assert(lct(0) == 9);
}

// line segment
unittest {
  auto lct = new LiChaoTree!Line(-10, 10);
  lct.add(-6, 6, new Line(1, 3));
  assert(lct(-7) == long.min);
  assert(lct(-6) == -3);
  assert(lct(5) == 8);
  assert(lct(6) == long.min);
  lct.add(-4, 0, new Line(2, 6));
  assert(lct(-5) == -2);
  assert(lct(-4) == -1);
  assert(lct(-3) == 0);
  assert(lct(-2) == 2);
  assert(lct(-1) == 4);
  assert(lct(0) == 3);
  lct.add(-2, 2, new Line(1, 4));
  assert(lct(-3) == 0);
  assert(lct(-2) == 2);
  assert(lct(-1) == 4);
  assert(lct(0) == 4);
  assert(lct(1) == 5);
  assert(lct(2) == 5);
  lct.add(-2, 1, new Line(5, 9));
  assert(lct(-3) == 0);
  assert(lct(-2) == 2);
  assert(lct(-1) == 4);
  assert(lct(0) == 9);
  assert(lct(1) == 5);
}

void main() {
}
