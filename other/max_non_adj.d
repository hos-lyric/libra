// T: signed integer
// ans[k]: max sum at k non-adjacent indexes  (0 <= k <= ceil(|as|/2))
// ans: concave
T[] maxNonAdj(T)(const(T[]) as) {
  import std.container : Array, BinaryHeap;
  import std.typecons : Tuple;
  const n = cast(int)(as.length);
  auto del = new bool[n + 2];
  auto lef = new int[n + 2], rig = new int[n + 2];
  foreach (i; 0 .. n + 2) {
    lef[i] = i - 1;
    rig[i] = i + 1;
  }
  auto ds = new T[n + 2];
  alias Entry = Tuple!(T, "val", int, "pos");
  BinaryHeap!(Array!Entry, "a.val < b.val") que;
  del[0] = del[n + 1] = true;
  foreach (i; 1 .. n + 1) que.insert(Entry(ds[i] = as[i - 1], i));
  auto ans = new T[(n + 1) / 2 + 1];
  for (int k = 0; !que.empty; ) {
    const i = que.front.pos;
    que.removeFront;
    if (!del[i]) {
      ans[k + 1] = ans[k] + ds[i];
      ++k;
      const l = lef[i], r = rig[i];
      if (1 <= l) {
        rig[lef[l]] = i;
        lef[i] = lef[l];
      }
      if (r <= n) {
        lef[rig[r]] = i;
        rig[i] = rig[r];
      }
      if (!del[l] && !del[r]) {
        que.insert(Entry(ds[i] = ds[l] + ds[r] - ds[i], i));
      } else {
        del[i] = true;
      }
      del[l] = del[r] = true;
    }
  }
  return ans;
}

////////////////////////////////////////////////////////////////////////////////

uint xrand() {
  static uint x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  uint t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

T[] brute(T)(const(T[]) as, T inf) {
  import std.algorithm : max;
  const n = cast(int)(as.length);
  auto dp = new T[][](n + 1, (n + 1) / 2 + 1);
  foreach (i; 0 .. n + 1) dp[i][] = -inf;
  dp[0][0] = 0;
  foreach (i; 0 .. n) {
    dp[i + 1][] = dp[i][];
    foreach (k; 1 .. (n + 1) / 2 + 1) {
      if (dp[i + 1][k] < dp[max(i - 1, 0)][k - 1] + as[i]) {
        dp[i + 1][k] = dp[max(i - 1, 0)][k - 1] + as[i];
      }
    }
  }
  return dp[n];
}

unittest {
  foreach (n; 0 .. 6 + 1) {
    // [0, 8)^n
    foreach (p; 0 .. 1 << (3 * n)) {
      auto as = new int[n];
      foreach (i; 0 .. n) as[i] = (p >> (3 * i) & 7) - 4;
      const expected = brute(as, 1001001001);
      const actual = maxNonAdj(as);
      assert(expected == actual);
      foreach (k; 0 .. (n + 1) / 2 - 1) {
        assert(actual[k + 1] - actual[k] >= actual[k + 2] - actual[k + 1]);
      }
    }
  }
  foreach (caseId; 0 .. 100) {
    const int n = 1 + xrand() % 100;
    auto as = new long[n];
    foreach (i; 0 .. n) as[i] = cast(int)(xrand());
    const expected = brute(as, 100100100100100101L);
    const actual = maxNonAdj(as);
    assert(expected == actual);
    foreach (k; 0 .. (n + 1) / 2 - 1) {
      assert(actual[k + 1] - actual[k] >= actual[k + 2] - actual[k + 1]);
    }
  }
}

// https://atcoder.jp/contests/joisc2018/tasks/joisc2018_j
void joisc2018_candies() {
  import core.stdc.stdio;
  int N;
  for (; ~scanf("%d", &N); ) {
    auto A = new long[N];
    foreach (i; 0 .. N) scanf("%lld", &A[i]);
    const ans = maxNonAdj(A);
    foreach (k; 1 .. (N + 1) / 2 + 1) printf("%lld\n", ans[k]);
    foreach (k; 0 .. (N + 1) / 2 - 1) {
      assert(ans[k + 1] - ans[k] >= ans[k + 2] - ans[k + 1]);
    }
  }
}

void main() {
  joisc2018_candies();
}
