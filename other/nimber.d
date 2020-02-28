// 2^i \otimes 2^j, a \otimes b
ulong[][] NIM_MUL_BASE, NIM_MUL_SMALL;
// (2^8)^i \otimes (2^8)^j \otimes a
ulong[][][] NIM_MUL_TABLE;

void prepareNimber() {
  import core.bitop : bsr;
  NIM_MUL_BASE = new ulong[][](64, 64);
  foreach (i; 0 .. 64) {
    NIM_MUL_BASE[0][i] = NIM_MUL_BASE[i][0] = 1UL << i;
  }
  foreach (i; 1 .. 64) foreach (j; 1 .. 64) {
    const n = bsr(i | j);
    if (i < 1 << n) {
      NIM_MUL_BASE[i][j] = NIM_MUL_BASE[i][j ^ 1 << n] << (1 << n);
    } else if (j < 1 << n) {
      NIM_MUL_BASE[i][j] = NIM_MUL_BASE[i ^ 1 << n][j] << (1 << n);
    } else {
      foreach (k; 0 .. 64) {
        if (NIM_MUL_BASE[i ^ 1 << n][j ^ 1 << n] & 1UL << k) {
          NIM_MUL_BASE[i][j] ^= NIM_MUL_BASE[k][1 << n];
          NIM_MUL_BASE[i][j] ^= NIM_MUL_BASE[k][(1 << n) - 1];
        }
      }
    }
  }
  NIM_MUL_SMALL = new ulong[][](256, 256);
  foreach (i; 0 .. 8) foreach (j; 0 .. 8) {
    NIM_MUL_SMALL[1 << i][1 << j] = NIM_MUL_BASE[i][j];
  }
  foreach (a; 1 .. 256) foreach (b; 1 .. 256) {
    if (b & b - 1) {
      NIM_MUL_SMALL[a][b] =
          NIM_MUL_SMALL[a][b & -b] ^ NIM_MUL_SMALL[a][b & b - 1];
    } else {
      NIM_MUL_SMALL[a][b] =
          NIM_MUL_SMALL[a & -a][b] ^ NIM_MUL_SMALL[a & a - 1][b];
    }
  }
  NIM_MUL_TABLE = new ulong[][][](8, 8, 256);
  foreach (i; 0 .. 8) foreach (j; 0 .. 8) {
    foreach (k; 0 .. 8) {
      NIM_MUL_TABLE[i][j][1 << k] = NIM_MUL_BASE[8 * i][8 * j + k];
    }
    foreach (a; 1 .. 256) {
      NIM_MUL_TABLE[i][j][a] =
          NIM_MUL_TABLE[i][j][a & -a] ^ NIM_MUL_TABLE[i][j][a & a - 1];
    }
  }
}

ulong nimMul(ulong a, ulong b) {
  ulong c;
  foreach (i; 0 .. 8) foreach (j; 0 .. 8) {
    c ^= NIM_MUL_TABLE[i][j][cast(uint)(
        NIM_MUL_SMALL[(a >> (8 * i)) & 255][(b >> (8 * j)) & 255])];
  }
  return c;
}

unittest {
  prepareNimber();
  assert(NIM_MUL_BASE[1][1] == 3UL);
  assert(NIM_MUL_BASE[63][63] == 16017865340936038689UL);
  assert(nimMul(5, 0) == 0);
  assert(nimMul(5, 1) == 5);
  assert(nimMul(5, 2) == 10);
  assert(nimMul(5, 3) == 15);
  assert(nimMul(5, 4) == 2);
  assert(nimMul(5, 5) == 7);
  assert(nimMul(5, 6) == 8);
  assert(nimMul(5, 7) == 13);
  assert(nimMul(5, 8) == 3);
  assert(nimMul(3141, 5926) == 14994);
  assert(nimMul(~0UL, ~0UL) == 11290409524105353207UL);
}

void main() {
}
