import mod_inv;

// modInv
unittest {
  for (long a = -99; a <= 99; a += 2) {
    assert(a * modInv(a) == 1);
  }
  assert(123456789123456789L * modInv(123456789123456789L) == 1);
  foreach (m; 1 .. 10) {
    foreach (a; -9 .. 100) {
      bool coprime = true;
      foreach (g; 2 .. 100) {
        if (m % g == 0 && a % g == 0) {
          coprime = false;
        }
      }
      if (coprime) {
        const b = modInv(a, m);
        assert(0 <= b && b < m);
        assert((a * b - 1) % m == 0);
      }
    }
  }
}

void main() {
}
