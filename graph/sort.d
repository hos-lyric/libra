// Sorts as so that for any adjacent elements a, b in this order,
// comp(a, b) || !comp(b, a)
//   buffer[0, floor(|as| / 2))  must be available.
//   <= (|as| (ceil(log_2 |as|) - 1) + 1) calls to comp for |as| >= 1
void mergeSort(alias comp = "a < b", T)(T[] as, T[] buffer) {
  import std.functional : binaryFun;
  const asLen = cast(int)(as.length);
  if (asLen >= 2) {
    const half = asLen / 2;
    mergeSort!comp(as[0 .. half], buffer);
    mergeSort!comp(as[half .. asLen], buffer);
    int i, j, k, l;
    for (; j != half; ) buffer[l++] = as[j++];
    for (; k != l && j != asLen; ) as[i++] = binaryFun!comp(as[j], buffer[k]) ? as[j++] : buffer[k++];
    for (; k != l; ) as[i++] = buffer[k++];
  }
}
void mergeSort(alias comp = "a < b", T)(T[] as) {
  mergeSort!comp(as, new T[as.length / 2]);
}

////////////////////////////////////////////////////////////////////////////////

uint xrand() {
  static uint x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  uint t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

unittest {
  {
    int[][] seqs = [
      [3, 1, 4, 1, 5, 9],
      [2, 6, 5, 3, 5],
      [8, 9, 7, 9],
      [3, 2, 3],
      [8, 4],
      [6],
    ];
    mergeSort(seqs);
    assert(seqs[0] == [2, 6, 5, 3, 5]);
    assert(seqs[1] == [3, 1, 4, 1, 5, 9]);
    assert(seqs[2] == [3, 2, 3]);
    assert(seqs[3] == [6]);
    assert(seqs[4] == [8, 4]);
    assert(seqs[5] == [8, 9, 7, 9]);
  }
  {
    foreach (N; 0 .. 100 + 1) {
      int e;
      for (; !(N <= 1 << e); ++e) {}
      foreach (caseId; 0 .. 100) {
        auto graph = new char[][](N, N);
        foreach (u; 0 .. N) {
          graph[u][] = '0';
        }
        foreach (u; 0 .. N) foreach (v; u + 1 .. N) {
          final switch (xrand() % 3) {
            case 0: break;
            case 1: graph[u][v] = '1'; break;
            case 2: graph[v][u] = '1'; break;
          }
        }
        auto us = new int[N];
        foreach (u; 0 .. N) {
          us[u] = u;
        }
        // us.mergeSort!((u, v) => (graph[u][v] == '1'));
        int numCalls;
        us.mergeSort!((u, v) {
          ++numCalls;
          return (graph[u][v] == '1');
        });
        assert(numCalls <= N * (e - 1) + 1);
        auto cnt = new int[N];
        foreach (j; 0 .. N) {
          assert(0 <= us[j]); assert(us[j] < N);
          ++cnt[us[j]];
        }
        foreach (u; 0 .. N) {
          assert(cnt[u] == 1);
        }
        foreach (j; 0 .. N - 1) {
          assert(graph[us[j]][us[j + 1]] == '1' || graph[us[j + 1]][us[j]] != '1');
        }
      }
    }
  }
}

void main() {
}
