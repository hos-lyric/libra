// |as| = n ==> |rs| = 2 n + 1
// [i - rs[i], i + rs[i]] is palindrome for $ as[0] $ as[1] $ ... $ as[n-1] $
// as[i, j): palindrome <=> j - i <= rs[i + j]
int[] manacher(String)(const(String) as) {
  const n = cast(int)(as.length);
  auto rs = new int[2 * n + 1];
  for (int i = 0, j = 0, k; i <= 2 * n; i += k, j -= k) {
    for (; 0 < i - j && i + j < 2 * n &&
           (!((i + j + 1) & 1) || as[(i - j - 1) >> 1] == as[(i + j + 1) >> 1]);
         ++j) {}
    rs[i] = j;
    for (k = 1; k < j && k + rs[i - k] < j; ++k) rs[i + k] = rs[i - k];
  }
  return rs;
}

// f(i, j) should check whether [i, j] (inclusive) is palindrome,
// assuming [i+1, j-1] is palindrome.
// Properties used:
//   rs[i] == i  (mod 2)
//   k + rs[i-k] <  rs[i] ==> rs[i+k] = rs[i-k]
//   k + rs[i-k] >= rs[i] ==> rs[i-k] >= rs[i] - k
// rs[2 * i + 1] = -1 is allowed (meaning [i, i] is not palindromic).
int[] manacher(Extend)(int n, Extend extend) {
  auto rs = new int[2 * n + 1];
  for (int i = 0, j = 0, k; i <= 2 * n; i += k, j -= k) {
    for (; 0 < i - j && i + j < 2 * n &&
           (j < -1 || !((i + j + 1) & 1) || extend((i - j - 1) >> 1, (i + j + 1) >> 1));
         ++j) {}
    rs[i] = j;
    for (k = 1; k < j && k + rs[i - k] < j; ++k) rs[i + k] = rs[i - k];
  }
  return rs;
}

////////////////////////////////////////////////////////////////////////////////

import std.stdio;

unittest {
  assert(manacher("sismississippi") == [
  //    s   i   s   m   i   s   s   i   s   s   i   p   p   i  
      0,1,0,3,0,1,0,1,0,1,0,1,4,1,0,7,0,1,4,1,0,1,0,1,4,1,0,1,0]);
  foreach (n; 0 .. 9 + 1) {
    foreach (p; 0 .. 1 << (2 * n)) {
      string s;
      foreach (i; 0 .. n) s ~= cast(char)('0' + (p >> (2 * i) & 3));
      auto isPalin = new int[][](n + 1, n + 1);
      foreach_reverse (i; 0 .. n + 1) foreach (j; i .. n + 1) {
        isPalin[i][j] = (j - i <= 1 || (s[i] == s[j - 1] && isPalin[i + 1][j - 1])) ? 1 : 0;
      }
      auto expected = new int[2 * n + 1];
      foreach (i; 0 .. n + 1) foreach (j; i .. n + 1) if (isPalin[i][j]) {
        if (expected[i + j] < j - i) expected[i + j] = j - i;
      }
      const actual = manacher(s);
      assert(expected == actual);
    }
  }
  foreach (n; 0 .. 8 + 1) {
    int numCases;
    auto rs = new int[2 * n + 1];
    void dfs(int pos) {
      if (pos == 2 * n + 1) {
        bool isValid() {
          foreach (i; 0 .. 2 * n + 1) {
            foreach (k; 1 .. rs[i]) {
              if (k + rs[i - k] <  rs[i] && !(rs[i + k] == rs[i - k])) return false;
              if (k + rs[i - k] >= rs[i] && !(rs[i + k] >= rs[i] - k)) return false;
            }
          }
          return true;
        }
        if (isValid) {
          assert(manacher(n, (int i, int j) {
            assert(i <= j);
            return (j - i + 1 <= rs[i + j + 1]);
          }) == rs);
          ++numCases;
        }
      } else {
        for (int r = -(pos & 1); r <= pos && r <= 2 * n - pos; r += 2) {
          rs[pos] = r;
          dfs(pos + 1);
        }
      }
    }
    dfs(0);
    stderr.writefln("[unittest_manacher] n = %s: %s cases", n, numCases);
    stderr.flush;
  }
}

void main() {
}
