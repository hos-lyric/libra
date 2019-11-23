// floor(a / b)
Int divFloor(Int)(Int a, Int b) {
  return a / b - (((a ^ b) < 0 && a % b != 0) ? 1 : 0);
}

// ceil(a / b)
Int divCeil(Int)(Int a, Int b) {
  return a / b + (((a ^ b) > 0 && a % b != 0) ? 1 : 0);
}

unittest {
  import std.math : floor, ceil;
  assert(divFloor(+13, +5) == +2);
  assert(divFloor(+13, -5) == -3);
  assert(divFloor(-13, +5) == -3);
  assert(divFloor(-13, -5) == +2);
  assert(divFloor(+20, +5) == +4);
  assert(divFloor(+20, -5) == -4);
  assert(divFloor(-20, +5) == -4);
  assert(divFloor(-20, -5) == +4);
  assert(divCeil(+13, +5) == +3);
  assert(divCeil(+13, -5) == -2);
  assert(divCeil(-13, +5) == -2);
  assert(divCeil(-13, -5) == +3);
  assert(divCeil(+20, +5) == +4);
  assert(divCeil(+20, -5) == -4);
  assert(divCeil(-20, +5) == -4);
  assert(divCeil(-20, -5) == +4);
  foreach (a; -100 .. 100) foreach (b; -100 .. 100) {
    if (b != 0) {
      assert(divFloor(a, b) == floor(cast(real)(a) / cast(real)(b)));
      assert(divCeil(a, b) == ceil(cast(real)(a) / cast(real)(b)));
    }
  }
}

void main() {
}
