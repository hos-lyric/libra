#ifndef LIBRA_SUFFIX_ARRAY_H_
#define LIBRA_SUFFIX_ARRAY_H_

#include <string.h>
#include <algorithm>
#include <string>
#include <utility>
#include <vector>

using std::min;
using std::string;
using std::swap;
using std::vector;

////////////////////////////////////////////////////////////////////////////////
// SA-IS
//   String: string, vector<int>, vector<long long>
//   if sigma <= n,  O(n) time, O(n) space
//   if sigma >  n,  O(n log n) time, O(n) space
template <class String> vector<int> suffixArrayRec(const String &as) {
  const int n = as.size();
  if (n == 0) return {};
  auto minA = as[0], maxA = as[0];
  for (int u = 0; u < n; ++u) {
    if (minA > as[u]) minA = as[u];
    if (maxA < as[u]) maxA = as[u];
  }
  if (static_cast<unsigned long long>(maxA) - minA >=
      static_cast<unsigned long long>(n)) {
    vector<int> us(n);
    for (int u = 0; u < n; ++u) us[u] = u;
    std::sort(us.begin(), us.end(), [&](int u, int v) -> bool {
      return (as[u] < as[v]);
    });
    int b = 0;
    vector<int> bs(n, 0);
    for (int i = 1; i < n; ++i) {
      if (as[us[i - 1]] != as[us[i]]) ++b;
      bs[us[i]] = b;
    }
    return suffixArrayRec(bs);
  }
  const int sigma = maxA - minA + 1;
  vector<int> pt(sigma + 1, 0), poss(sigma);
  for (int u = 0; u < n; ++u) ++pt[as[u] - minA + 1];
  for (int a = 0; a < sigma; ++a) pt[a + 1] += pt[a];
  // cmp[u] := (as[u, n) < as[u + 1, n))
  vector<bool> cmp(n);
  cmp[n - 1] = false;
  for (int u = n - 1; --u >= 0; ) {
    cmp[u] = (as[u] != as[u + 1]) ? (as[u] < as[u + 1]) : cmp[u + 1];
  }
  // ><,  nn - id (0 <= id < n)
  int nn = 0;
  vector<int> ids(n, 0);
  int last = n;
  vector<int> nxt(n, 0);
  // put ><, from the tail of each bucket
  vector<int> us(n, 0);
  memcpy(poss.data(), pt.data() + 1, sigma * sizeof(int));
  for (int u = n - 1; --u >= 1; ) if (!cmp[u - 1] && cmp[u]) {
    ids[u] = ++nn;
    nxt[u] = last;
    last = u;
    us[--poss[as[u] - minA]] = u;
  }
  // follow > backwards, from the head of each bucket
  memcpy(poss.data(), pt.data(), sigma * sizeof(int));
  us[poss[as[n - 1] - minA]++] = n - 1;
  for (int i = 0; i < n; ++i) {
    const int u = us[i];
    if (u && !cmp[u - 1]) us[poss[as[u - 1] - minA]++] = u - 1;
  }
  // follow < backwards, from the tail of each bucket
  memcpy(poss.data(), pt.data() + 1, sigma * sizeof(int));
  for (int i = n; --i >= 0; ) {
    const int u = us[i];
    if (u && cmp[u - 1]) us[--poss[as[u - 1] - minA]] = u - 1;
  }
  if (nn) {
    int vsLen = 0;
    vector<int> vs(nn);
    for (const int u : us) if (ids[u]) vs[vsLen++] = u;
    int b = 0;
    vector<int> bs(nn, 0);
    for (int j = 1; j < nn; ++j) {
      // as[v1, w1] (< or =) as[v0, w0]
      int v1 = vs[j - 1], v0 = vs[j];
      const int w1 = nxt[v1], w0 = nxt[v0];
      if (w1 - v1 != w0 - v0) {
        ++b;
      } else {
        for (; ; ++v1, ++v0) {
          if (v1 == n) { ++b; break; }
          if (as[v1] != as[v0]) { ++b; break; }
          if (v1 == w1) break;
        }
      }
      bs[nn - ids[vs[j]]] = b;
    }
    for (int u = 0; u < n; ++u) if (ids[u]) vs[nn - ids[u]] = u;
    const auto sub = suffixArrayRec(bs);
    // put ><, from the tail of each bucket
    memset(us.data(), 0, n * sizeof(int));
    memcpy(poss.data(), pt.data() + 1, sigma * sizeof(int));
    for (int j = nn; --j >= 0; ) {
      const int u = vs[sub[j]];
      us[--poss[as[u] - minA]] = u;
    }
    // follow > backwards, from the head of each bucket
    memcpy(poss.data(), pt.data(), sigma * sizeof(int));
    us[poss[as[n - 1] - minA]++] = n - 1;
    for (int i = 0; i < n; ++i) {
      const int u = us[i];
      if (u && !cmp[u - 1]) us[poss[as[u - 1] - minA]++] = u - 1;
    }
    // follow < backwards, from the tail of each bucket
    memcpy(poss.data(), pt.data() + 1, sigma * sizeof(int));
    for (int i = n; --i >= 0; ) {
      const int u = us[i];
      if (u && cmp[u - 1]) us[--poss[as[u - 1] - minA]] = u - 1;
    }
  }
  return us;
}

// us[i]: i-th suffix
// su[u]: index of as[u, n)
// hs[i]: longest common prefix of as[us[i - 1], n) and as[us[i], n)
struct SuffixArray {
  int n;
  bool rmq;
  vector<int> us, su, hs;
  SuffixArray() : n(0), rmq(false) {}
  SuffixArray(const string &as, bool rmq_) : rmq(rmq_) { build(as); }
  SuffixArray(const vector<int> &as, bool rmq_) : rmq(rmq_) { build(as); }
  SuffixArray(const vector<long long> &as, bool rmq_) : rmq(rmq_) { build(as); }
  template <class String> void build(const String &as) {
    n = as.size();
    us = suffixArrayRec(as);
    su.resize(n + 1);
    for (int i = 0; i < n; ++i) su[us[i]] = i;
    su[n] = -1;
    hs.assign(n, 0);
    for (int h = 0, u = 0; u < n; ++u) if (su[u]) {
      for (int v = us[su[u] - 1]; v + h < n && as[v + h] == as[u + h]; ++h) {}
      hs[su[u]] = h;
      if (h) --h;
    }
    if (rmq) {
      const int logN = n ? (31 - __builtin_clz(n)) : 0;
      hs.resize((logN + 1) * n - (1 << logN) + 1);
      for (int e = 0; e < logN; ++e) {
        int *hes = hs.data() + e * n;
        for (int i = 0; i <= n - (1 << (e + 1)); ++i) {
          hes[n + i] = min(hes[i], hes[i + (1 << e)]);
        }
      }
    }
  }
  // Returns longest common prefix of as[u, n) and as[v, n).
  //   0 <= u, v <= n
  //   Assumes rmq.
  inline int lcp(int u, int v) const {
    if (u == v) return n - u;
    int i = su[u], j = su[v];
    if (i > j) swap(i, j);
    const int e = 31 - __builtin_clz(j - i);
    return min(hs[e * n + i + 1], hs[e * n + j + 1 - (1 << e)]);
  }
};
////////////////////////////////////////////////////////////////////////////////

#endif  // LIBRA_SUFFIX_ARRAY_H_
