#include <assert.h>
#include <algorithm>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

#include "suffix_array.h"

using std::ostream;
using std::min;
using std::max;
using std::pair;
using std::string;
using std::vector;

// before HLD:
//   0 <= u <= n: suffix [u, n)  (n: root, empty string)
//   n <  u <  m: LCA needed
// after HLD:
//   DFS-order
//   0: root, empty string
//   perm[u]: suffix[u, n)  (0 <= u <= n)
struct SuffixTree {
  int n, m;
  SuffixArray sa;
  struct Node {
    int par, len, occ;
    inline int l() const { return occ; }
    inline int r() const { return occ + len; }
  };
  vector<Node> nodes;
  vector<int> perm;
  SuffixTree() {}
  SuffixTree(const string &str, bool lastOcc) { build(str, lastOcc); }
  SuffixTree(const vector<int> &str, bool lastOcc) { build(str, lastOcc); }
  SuffixTree(const vector<long long> &str, bool lastOcc) { build(str, lastOcc); }
  template <class String> void build(const String &str, bool lastOcc) {
    n = str.size();
    m = n + 1;
    sa = SuffixArray(str, /*rmq=*/false);
    nodes.resize(2 * n + 1);
    nodes[n] = Node{/*par=*/-1, /*len=*/0, /*occ=*/lastOcc ? n : 0};
    int top = 0;
    vector<int> stack(n + 1);
    stack[0] = n;
    for (int i = 0; i < n; ++i) {
      const int u = sa.us[i];
      int v = -1;
      for (; nodes[stack[top]].len > sa.hs[i]; --top) {
        v = stack[top];
        nodes[nodes[v].par].occ = lastOcc ? max(nodes[nodes[v].par].occ, nodes[v].occ) : min(nodes[nodes[v].par].occ, nodes[v].occ);
      }
      if (nodes[stack[top]].len < sa.hs[i]) {
        const int w = m++;
        nodes[w] = Node{/*par=*/nodes[v].par, /*len=*/sa.hs[i], /*occ=*/nodes[v].occ};
        stack[++top] = nodes[v].par = w;
      }
      nodes[u] = Node{/*par=*/stack[top], /*len=*/n - u, /*occ=*/u};
      stack[++top] = u;
    }
    for (; top; --top) {
      const int v = stack[top];
      nodes[nodes[v].par].occ = lastOcc ? max(nodes[nodes[v].par].occ, nodes[v].occ) : min(nodes[nodes[v].par].occ, nodes[v].occ);
    }
    nodes.resize(m);
    runHld();
  }
  inline const Node &operator[](int u) const {
    return nodes[u];
  }
  inline int size(int u) const {
    return (~nodes[u].par) ? (nodes[u].len - nodes[nodes[u].par].len) : 1;
  }

  // Reindexes nodes by DFS-order.
  //   Ignores character order.
  //   Subtrees at the same "color" are isomorphic, should have the same HLD.
  //   old u -> new perm[u]
  vector<int> pt, g, head;
  void runHld() {
    pt.assign(m + 1, 0);
    for (int u = 0; u < m; ++u) if (u != n) ++pt[nodes[u].par];
    for (int u = 0; u < m; ++u) pt[u + 1] += pt[u];
    g.resize(pt[m]);
    for (int u = m; --u >= 0; ) if (u != n) g[--pt[nodes[u].par]] = u;
    vector<int> sz(m, 1);
    dfsSz(n, sz);
    int zeit = 0;
    perm.resize(m);
    head.resize(m);
    head[n] = 0;
    dfsHld(n, zeit, sz);
    assert(zeit == m);
    vector<Node> nodesReindexed(m);
    for (int u = 0; u < m; ++u) {
      Node &node = nodesReindexed[perm[u]] = nodes[u];
      if (~node.par) node.par = perm[node.par];
    }
    nodes.swap(nodesReindexed);
    for (int u = 0; u <= m; ++u) pt[u] = 0;
    for (int u = 1; u < m; ++u) ++pt[nodes[u].par];
    for (int u = 1; u < m; ++u) pt[u + 1] += pt[u];
    g.resize(pt[m]);
    for (int u = m; --u >= 1; ) g[--pt[nodes[u].par]] = u;
  }
  void dfsSz(int u, vector<int> &sz) {
    for (int i = pt[u]; i < pt[u + 1]; ++i) {
      dfsSz(g[i], sz);
      sz[u] += sz[g[i]];
    }
  }
  void dfsHld(int u, int &zeit, vector<int> &sz) {
    perm[u] = zeit++;
    if (pt[u] < pt[u + 1]) {
      int im = pt[u];
      for (int i = pt[u] + 1; i < pt[u + 1]; ++i) if (sz[g[im]] < sz[g[i]]) im = i;
      swap(g[pt[u]], g[im]);
      head[zeit] = head[zeit - 1];
      dfsHld(g[pt[u]], zeit, sz);
      for (int i = pt[u] + 1; i < pt[u + 1]; ++i) {
        head[zeit] = zeit;
        dfsHld(g[i], zeit, sz);
      }
    }
  }
  // Returns the shallowest node representing [l, r') for r <= r'.
  int locate(int l, int r) const {
    assert(0 <= l); assert(l <= r); assert(r <= n);
    for (int u = perm[l]; ; ) {
      const int h = head[u];
      const int p = nodes[h].par;
      if (!~p || nodes[p].len < r - l) {
        int lo = h - 1, hi = u;
        for (; lo + 1 < hi; ) {
          const int mid = (lo + hi) / 2;
          ((nodes[mid].len < r - l) ? lo : hi) = mid;
        }
        return hi;
      }
      u = p;
    }
  }
};

// block i contains [ls[i] + x, rs[i] - y) s.t.
//   0 <= x < sizeL(i),  0 <= y < sizeR(i, x)
//   0 <= y < sizeR(i),  0 <= x < sizeL(i, y)
struct Substring {
  // |str|
  int n;
  // stRev: occ is modified to represent the first occurrence in str
  SuffixTree st, stRev;
  // # of colors
  int size;
  // tree node -> block id
  vector<int> is, isRev;
  // [ls[i], rs[i]): representative of block i, i.e. [min l, max r)
  vector<int> ls, rs;
  // tree nodes for block i: us[js[i], js[i] + sizeL(i)), usRev[jsRev[i], jsRev[i] + sizeR(i))
  vector<int> js, jsRev, us, usRev;
  Substring() {}
  Substring(const string &str) { build(str); }
  Substring(const vector<int> &str) { build(str); }
  Substring(const vector<long long> &str) { build(str); }
  // O(n) time
  template <class String> void build(const String &str) {
    n = str.size();
    st = SuffixTree(str, /*lastOcc=*/false);
    String strRev = str;
    std::reverse(strRev.begin(), strRev.end());
    stRev = SuffixTree(strRev, /*lastOcc=*/true);
    for (int u = 0; u < stRev.m; ++u) stRev.nodes[u].occ = n - stRev.nodes[u].r();
    size = 0;
    is.assign(st.m, -1);
    isRev.assign(stRev.m, -1);
    js = jsRev = {1};
    us.assign(st.m, 0);
    usRev.assign(stRev.m, 0);
    {
      // radix sort: incr len, incr occ
      const int seqLen = (st.m - 1) + (stRev.m - 1);
      vector<int> ptLen(n + 1, 0), ptOcc(n + 1, 0);
      for (int u = 1; u < st.m; ++u) { ++ptLen[st[u].len]; ++ptOcc[st[u].occ]; }
      for (int u = 1; u < stRev.m; ++u) { ++ptLen[stRev[u].len]; ++ptOcc[stRev[u].occ]; }
      for (int len = 0; len < n; ++len) ptLen[len + 1] += ptLen[len];
      for (int occ = 0; occ < n; ++occ) ptOcc[occ + 1] += ptOcc[occ];
      vector<int> work(seqLen);
      for (int u = stRev.m; --u >= 1; ) work[--ptOcc[stRev[u].occ]] = ~u;
      for (int u = st.m; --u >= 1; ) work[--ptOcc[st[u].occ]] = u;
      vector<int> seq(seqLen);
      for (int k = seqLen; --k >= 0; ) seq[--ptLen[(work[k] >= 0) ? st[work[k]].len : stRev[~work[k]].len]] = work[k];
      for (int k = 0; k < seqLen - 1; ++k) if (seq[k] >= 0 && seq[k + 1] < 0 && st[seq[k]].len == stRev[~seq[k + 1]].len && st[seq[k]].occ == stRev[~seq[k + 1]].occ) {
        ls.push_back(st[seq[k]].l());
        rs.push_back(st[seq[k]].r());
        js.push_back(js.back() + stRev.size(~seq[k + 1]));
        jsRev.push_back(jsRev.back() + st.size(seq[k]));
        is[seq[k]] = isRev[~seq[k + 1]] = size++;
      }
    }
    {
      // radix sort: incr r, incr l
      const int seqLen = st.m - 1;
      vector<int> ptL(n + 1, 0), ptR(n + 1, 0);
      for (int u = 1; u < st.m; ++u) { ++ptL[st[u].l()]; ++ptR[st[u].r()]; }
      for (int l = 0; l < n; ++l) ptL[l + 1] += ptL[l];
      for (int r = 0; r < n; ++r) ptR[r + 1] += ptR[r];
      vector<int> work(seqLen);
      for (int u = st.m; --u >= 1; ) work[--ptL[st[u].l()]] = u;
      vector<int> seq(seqLen);
      for (int k = seqLen; --k >= 0; ) seq[--ptR[st[work[k]].r()]] = work[k];
      int i = -1, j = 0;
      for (int k = 0; k < seqLen; ++k) {
        if (~is[seq[k]]) j = js[i = is[seq[k]]];
        is[us[j++] = seq[k]] = i;
      }
    }
    {
      // radix sort: decr l, decr r
      const int seqLen = stRev.m - 1;
      vector<int> ptL(n + 1, 0), ptR(n + 1, 0);
      for (int u = 1; u < stRev.m; ++u) { ++ptL[stRev[u].l()]; ++ptR[stRev[u].r()]; }
      for (int l = n; l > 0; --l) ptL[l - 1] += ptL[l];
      for (int r = n; r > 0; --r) ptR[r - 1] += ptR[r];
      vector<int> work(seqLen);
      for (int u = stRev.m; --u >= 1; ) work[--ptR[stRev[u].r()]] = u;
      vector<int> seq(seqLen);
      for (int k = seqLen; --k >= 0; ) seq[--ptL[stRev[work[k]].l()]] = work[k];
      int i = -1, j = 0;
      for (int k = 0; k < seqLen; ++k) {
        if (~isRev[seq[k]]) j = jsRev[i = isRev[seq[k]]];
        isRev[usRev[j++] = seq[k]] = i;
      }
    }
  }
  // block id at representative position
  // st node id
  // stRev node id
  friend ostream &operator<<(ostream &os, const Substring &sub) {
    const int width = max(static_cast<int>(std::to_string(max(sub.st.m, sub.stRev.m) - 1).size()) + 1, 3);
    for (int phase = 0; phase < 3; ++phase) {
      for (int r = sub.n; r > 0; --r) {
        for (int l = 0; l < r; ++l) {
          const Location loc = sub.locate(l, r);
          string s;
          switch (phase) {
            case 0: {
              if (sub.ls[loc.i] == l && sub.rs[loc.i] == r) s = std::to_string(loc.i);
            } break;
            case 1: {
              if (sub.st[loc.u].len == r - l) s = std::to_string(loc.u);
            } break;
            case 2: {
              if (sub.stRev[loc.v].len == r - l) s = std::to_string(loc.v);
            } break;
          }
          os << "\x1b[" << (41 + loc.i % 6) << "m";
          os << string(width - static_cast<int>(s.size()), ' ') << s;
          os << "\x1b[m";
        }
        os << '\n';
      }
      os << '\n';
    }
    return os;
  }
  inline int id(int i, int x = 0) const {
    return us[js[i] + x];
  }
  inline int idRev(int i, int y = 0) const {
    return usRev[jsRev[i] + y];
  }
  inline int sizeR(int i, int x = 0) const {
    return st.size(id(i, x));
  }
  inline int sizeL(int i, int y = 0) const {
    return stRev.size(idRev(i, y));
  }
  // i: block id
  // x, y: coordinate within block i, [ls[i] + x, rs[i] - y)
  // u = st.locate(l, r)           : shallowest node of st    for [l, r') s.t. r <= r'
  // v = stRev.locate(n - r, n - l): shallowest node of stRev for [l', r) s.t. l' <= l
  // O(log(n)) time
  struct Location {
    int i, x, y, u, v;
  };
  Location locate(int l, int r) const {
    assert(0 <= l); assert(l <= r); assert(r <= n);
    if (l == r) return Location{-1, 0, 0, 0, 0};
    Location loc;
    loc.u = st.locate(l, r);
    loc.i = is[loc.u];
    loc.x = st[loc.u].l() - ls[loc.i];
    loc.y = ((l - loc.x) + (rs[loc.i] - ls[loc.i])) - r;
    loc.v = idRev(loc.i, loc.y);
    return loc;
  }

  // pattern ([l, r), t): (weight of str[l, r)) += t
  //   l < r
  //   T: commutative group
  // query [l, r): \sum[l<=l'<r'<=r] (weight of str[l', r'))
  // O(n + (|patterns| + |queries|) log(n)) time
  template <class T>
  vector<T> countOffline(const vector<pair<pair<int, int>, T>> &patterns,
                         const vector<pair<int, int>> &queries) const {
    const int patternsLen = patterns.size();
    const int queriesLen = queries.size();
    // x -> ((y, p or ~q))
    vector<vector<pair<int, int>>> eventss(st.m);
    // tree DP (path to root)
    vector<T> dp(st.m), dpRev(stRev.m);
    for (int p = 0; p < patternsLen; ++p) {
      const int l = patterns[p].first.first, r = patterns[p].first.second;
      assert(0 <= l); assert(l < r); assert(r <= n);
      const Location loc = locate(l, r);
      eventss[js[loc.i] + loc.x].emplace_back(loc.y, p);
      dp[loc.u] += patterns[p].second;
      dpRev[loc.v] += patterns[p].second;
    }
    for (int u = 1; u < st.m; ++u) dp[u] += dp[st[u].par];
    for (int u = 1; u < stRev.m; ++u) dpRev[u] += dpRev[stRev[u].par];
    // query [ls[i], rs[i])
    vector<T> corner(size);
    for (int i = 0; i < size; ++i) {
      for (int x = 0; x < sizeL(i); ++x) corner[i] += dp[id(i, x)];
      const int ii = isRev[stRev[idRev(i)].par];
      if (~ii) corner[i] += corner[ii];
    }
    // query [ls[i], rs[i] - y)
    vector<T> edge(stRev.m);
    for (int i = 0; i < size; ++i) {
      const int ii = is[st[id(i)].par];
      T sum = (~ii) ? corner[ii] : T();
      for (int y = sizeR(i); --y >= 0; ) edge[jsRev[i] + y] = sum += dpRev[idRev(i, y)];
    }
    // suffix sum of dp[st[id(i, x)].par]
    // can use segment tree if subtraction is unavailable
    vector<T> sumPar(st.m);
    for (int i = 0; i < size; ++i) {
      T sum = T();
      for (int x = sizeL(i); --x >= 0; ) sumPar[js[i] + x] = sum += dp[st[id(i, x)].par];
    }
    // query [l, r)
    vector<T> ans(queriesLen);
    vector<int> hasQuery(size, 0);
    for (int q = 0; q < queriesLen; ++q) {
      const int l = queries[q].first, r = queries[q].second;
      assert(0 <= l); assert(l <= r); assert(r <= n);
      if (l < r) {
        const Location loc = locate(queries[q].first, queries[q].second);
        if (loc.x == 0) {
          if (loc.y == 0) {
            ans[q] += corner[loc.i];
          } else {
            ans[q] += edge[jsRev[loc.i] + loc.y];
          }
        } else {
          hasQuery[loc.i] = 1;
          eventss[js[loc.i] + loc.x].emplace_back(loc.y, ~q);
          ans[q] += sumPar[js[loc.i] + loc.x];
          if (sizeL(loc.i, loc.y) < sizeL(loc.i)) ans[q] -= sumPar[js[loc.i] + sizeL(loc.i, loc.y)];
          const int vv = stRev[loc.v].par;
          const int ii = isRev[vv];
          if (~ii) ans[q] += edge[jsRev[ii] + (rs[ii] - stRev[vv].r())];
        }
      }
    }
    // offline 2D
    vector<T> bit(n + 1);
    for (int i = 0; i < size; ++i) if (hasQuery[i]) {
      for (int y = 1; y <= sizeR(i); ++y) bit[y] = T();
      for (int x = sizeL(i); --x >= 0; ) for (const auto &event : eventss[js[i] + x]) {
        if (event.second >= 0) {
          const T t = patterns[event.second].second;
          for (int y = sizeR(i) - event.first; y <= sizeR(i); y += y & -y) bit[y] += t;
        } else {
          T sum = T();
          for (int y = sizeR(i) - event.first; y > 0; y &= y - 1) sum += bit[y];
          ans[~event.second] += sum;
        }
      }
    }
    return ans;
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <random>

using std::cerr;
using std::endl;

std::mt19937_64 rng;

// String: string, vector<int>, vector<long long>
template <class String> void test(const String &as) {
  const int n = as.size();
  vector<vector<int>> lcp(n + 1, vector<int>(n + 1, 0));
  for (int i = n; --i >= 0; ) for (int j = n; --j >= 0; ) {
    lcp[i][j] = (as[i] == as[j]) ? (1 + lcp[i + 1][j + 1]) : 0;
  }
  vector<vector<vector<int>>> occss(n + 1, vector<vector<int>>(n + 1));
  for (int i = 0; i <= n; ++i) for (int j = 0; j <= n; ++j) {
    for (int len = 0; len <= lcp[i][j]; ++len) {
      occss[i][i + len].push_back(j);
    }
  }
  vector<pair<int, int>> corners;
  for (int len = 1; len <= n; ++len) for (int l = 0; l <= n - len; ++l) {
    const int r = l + len;
    if (occss[l][r][0] != l) continue;
    if (l > 0 && occss[l - 1][r].size() == occss[l][r].size()) continue;
    if (r < n && occss[l][r + 1].size() == occss[l][r].size()) continue;
    corners.emplace_back(l, r);
  }

  // SuffixTree
  {
    SuffixTree st0(as, /*lastOcc=*/false), st1(as, /*lastOcc=*/true);
    const int m = st0.m;
    assert(st0.n == n);
    assert(st1.n == n);
    assert(st0.m == m);
    assert(st1.m == m);
    assert(static_cast<int>(st0.nodes.size()) == m);
    assert(static_cast<int>(st1.nodes.size()) == m);
    for (int u = 0; u < m; ++u) {
      if (u) {
        const int p = st0[u].par;
        assert(p < u);
        assert(st0[u].par == p);
        assert(st1[u].par == p);
        assert(st0[p].len < st0[u].len);
        assert(st1[p].len < st1[u].len);
        const int len = st0[u].len, occ = st0[u].occ;
        assert(0 <= occ); assert(occ <= occ + len); assert(occ + len <= n);
        const auto occs = occss[occ][occ + len];
        assert(st0[u].len == len);
        assert(st1[u].len == len);
        assert(st0[u].occ == occs[0]);
        assert(st1[u].occ == occs.back());
        assert(st0[u].l() == occs[0]);
        assert(st0[u].r() == occs[0] + len);
        assert(st1[u].l() == occs.back());
        assert(st1[u].r() == occs.back() + len);
      } else {
        assert(st0[u].par == -1);
        assert(st1[u].par == -1);
        assert(st0[u].len == 0);
        assert(st1[u].len == 0);
        assert(st0[u].occ == 0);
        assert(st1[u].occ == n);
      }
    }
    assert(st0.perm == st1.perm);
    assert(static_cast<int>(st0.perm.size()) == m);
    {
      vector<int> freq(m, 0);
      for (int u = 0; u < m; ++u) assert(++freq[st0.perm[u]] == 1);
    }
    for (int l = 0; l <= n; ++l) {
      assert(st0[st0.perm[l]].len == n - l);
      assert(st1[st1.perm[l]].len == n - l);
      assert(st0[st0.perm[l]].occ == occss[l][n][0]);
      assert(st1[st1.perm[l]].occ == l);
    }
    vector<vector<int>> uss(n + 1, vector<int>(n + 1, -1));
    for (int u = 0; u < m; ++u) for (int x = 0; x < st0.size(u); ++x) {
      int &v = uss[st0[u].occ][st0[u].occ + st0[u].len - x];
      assert(!~v);
      v = u;
    }
    for (int l = 0; l <= n; ++l) for (int r = l; r <= n; ++r) {
      const int u = uss[occss[l][r][0]][occss[l][r][0] + (r - l)];
      assert(~u);
      assert(st0.locate(l, r) == u);
      assert(st1.locate(l, r) == u);
    }
  }

  Substring sub(as);
  assert(sub.n == n);
  assert(sub.size == static_cast<int>(corners.size()));
  assert(static_cast<int>(sub.is.size()) == sub.st.m);
  assert(static_cast<int>(sub.isRev.size()) == sub.stRev.m);
  assert(sub.is[0] == -1);
  assert(sub.isRev[0] == -1);
  for (int i = 0; i < sub.size; ++i) {
    const int l = corners[i].first, r = corners[i].second;
    vector<int> freqX, freqY;
    for (int x = 0; l + x < r && occss[l + x][r].size() == occss[l][r].size(); ++x) freqX.push_back(0);
    for (int y = 0; l < r - y && occss[l][r - y].size() == occss[l][r].size(); ++y) freqY.push_back(0);
    for (int x = 0; l + x < r && occss[l + x][r].size() == occss[l][r].size(); ++x) {
      for (int y = 0; l + x < r - y && occss[l + x][r - y].size() == occss[l][r].size(); ++y) {
        ++freqX[x];
        ++freqY[y];
      }
    }
    assert(sub.ls[i] == l);
    assert(sub.rs[i] == r);
    assert(sub.sizeL(i) == static_cast<int>(freqX.size()));
    assert(sub.sizeR(i) == static_cast<int>(freqY.size()));
    for (int x = 0; x < sub.sizeL(i); ++x) assert(sub.sizeR(i, x) == freqX[x]);
    for (int y = 0; y < sub.sizeR(i); ++y) assert(sub.sizeL(i, y) == freqY[y]);
    for (int x = 0; x < sub.sizeL(i); ++x) {
      const int u = sub.id(i, x);
      assert(sub.is[u] == i);
      assert(sub.st[u].len == r - (l + x));
      assert(sub.st[u].occ == l + x);
    }
    for (int y = 0; y < sub.sizeR(i); ++y) {
      const int u = sub.idRev(i, y);
      assert(sub.isRev[u] == i);
      assert(sub.stRev[u].len == (r - y) - l);
      assert(sub.stRev[u].occ == l);
    }
  }
  for (int l = 0; l <= n; ++l) for (int r = l; r <= n; ++r) {
    int ll = l, rr = r;
    for (; rr < n && occss[l][rr + 1].size() == occss[l][rr].size(); ++rr) {}
    for (; ll > 0 && occss[ll - 1][r].size() == occss[ll][r].size(); --ll) {}
    const Substring::Location loc = sub.locate(l, r);
    if (l == r) {
      assert(loc.i == -1);
      assert(loc.x == 0);
      assert(loc.y == 0);
    } else {
      assert(0 <= loc.i); assert(loc.i < sub.size);
      assert(0 <= loc.x); assert(loc.x < sub.sizeL(loc.i));
      assert(0 <= loc.y); assert(loc.y < sub.sizeR(loc.i));
      assert(corners[loc.i].first == occss[ll][rr][0]);
      assert(corners[loc.i].second == occss[ll][rr][0] + (rr - ll));
      assert(corners[loc.i].first + loc.x == occss[l][r][0]);
      assert(corners[loc.i].second - loc.y == occss[l][r][0] + (r - l));
    }
    assert(0 <= loc.u); assert(loc.u < sub.st.m);
    assert(0 <= loc.v); assert(loc.v < sub.stRev.m);
    {
      const SuffixTree::Node &node = sub.st[loc.u];
      assert(node.len == rr - l);
      assert(node.occ == occss[l][rr][0]);
    }
    {
      const SuffixTree::Node &node = sub.stRev[loc.v];
      assert(node.len == r - ll);
      assert(node.occ == occss[ll][r][0]);
    }
  }

  // ensure: Subtrees at the same "color" are isomorphic, should have the same HLD.
  for (int i = 0; i < sub.size; ++i) {
    int l0 = -1, r0 = -1;
    for (int x = 0; x < sub.sizeL(i); ++x) {
      const int u = sub.id(i, x);
      if (sub.st.pt[u] < sub.st.pt[u + 1]) {
        // heavy child: u + 1
        const int r = sub.st[u + 1].r();
        const int l = r - (sub.st[u + 1].len - sub.st[u].len);
        if (x == 0) {
          l0 = l;
          r0 = r;
        }
        assert(r0 - l0 == r - l);
        assert(lcp[l0][l] >= r0 - l0);
      } else {
        // leaf
        assert(!~l0);
        assert(!~r0);
      }
    }
  }
  for (int i = 0; i < sub.size; ++i) {
    int l0 = -1, r0 = -1;
    for (int y = 0; y < sub.sizeR(i); ++y) {
      const int u = sub.idRev(i, y);
      if (sub.stRev.pt[u] < sub.stRev.pt[u + 1]) {
        // heavy child: u + 1
        const int l = sub.stRev[u + 1].l();
        const int r = l + (sub.stRev[u + 1].len - sub.stRev[u].len);
        if (y == 0) {
          l0 = l;
          r0 = r;
        }
        assert(r0 - l0 == r - l);
        assert(lcp[l0][l] >= r0 - l0);
      } else {
        // leaf
        assert(!~l0);
        assert(!~r0);
      }
    }
  }

  // Substring::countOffline
  for (int phase = 0; phase < 2; ++phase) {
    int patternsLen, queriesLen;
    vector<pair<pair<int, int>, unsigned long long>> patterns;
    vector<pair<int, int>> queries;
    if (phase == 0) {
      for (int l = 0; l <= n; ++l) for (int r = l; r <= n; ++r) {
        if (l < r) {
          patterns.emplace_back(std::make_pair(l, r), rng());
        }
        queries.emplace_back(l, r);
      }
      patternsLen = patterns.size();
      queriesLen = queries.size();
    } else {
      patternsLen = rng() % (2 * n * n + 1);
      queriesLen = rng() % (2 * n * n + 1);
      for (int p = 0; p < patternsLen; ++p) {
        for (; ; ) {
          const int l = rng() % (n + 1);
          const int r = rng() % (n + 1);
          if (l < r) {
            patterns.emplace_back(std::make_pair(l, r), rng());
            break;
          }
        }
      }
      for (int q = 0; q < queriesLen; ++q) {
        for (; ; ) {
          const int l = rng() % (n + 1);
          const int r = rng() % (n + 1);
          if (l <= r) {
            queries.emplace_back(l, r);
            break;
          }
        }
      }
    }
    vector<vector<unsigned long long>> expected(n + 1, vector<unsigned long long>(n + 1, 0));
    for (int p = 0; p < patternsLen; ++p) {
      const int l = patterns[p].first.first, r = patterns[p].first.second;
      for (int ll = 0; ll + (r - l) <= n; ++ll) if (lcp[l][ll] >= r - l) {
        expected[ll][ll + (r - l)] += patterns[p].second;
      }
    }
    for (int l = n; l > 0; --l) for (int r = l; r <= n; ++r) expected[l - 1][r] += expected[l][r];
    for (int l = 0; l <= n; ++l) for (int r = l; r < n; ++r) expected[l][r + 1] += expected[l][r];
    const vector<unsigned long long> actual = sub.countOffline(patterns, queries);
    assert(static_cast<int>(actual.size()) == queriesLen);
    for (int q = 0; q < queriesLen; ++q) {
      const int l = queries[q].first, r = queries[q].second;
      assert(actual[q] == expected[l][r]);
    }
  }
}

void testAllVectors(int n, int sigma) {
  vector<int> as(n, 0);
  for (; ; ) {
    test(as);
    for (int i = n; ; ) {
      if (i-- == 0) {
        cerr << "[testAllVectors] PASSED n = " << n << ", sigma = " << sigma << endl;
        return;
      }
      if (++as[i] < sigma) break;
      as[i] = 0;
    }
  }
}

void unittest() {
  {
    Substring sub("abbab");
    cerr << sub << std::flush;
    // 0                         
    // |-ab----- 4               
    // |         `-bab--------- 5
    // `-b- 1                    
    //      |-ab----- 3          
    //      `-bab--------- 2     
    // 0                         
    // |-a- 5                    
    // |    `-abb--------- 6     
    // `-b- 1                    
    //      |-a- 2               
    //      |    `-abb--------- 3
    //      `-ab----- 4          
    auto checkLocate = [&](int l, int r, int i, int x, int y, int u, int v) -> void {
      Substring::Location loc = sub.locate(l, r);
      assert(loc.i == i);
      assert(loc.x == x);
      assert(loc.y == y);
      assert(loc.u == u);
      assert(loc.v == v);
    };
    checkLocate(0, 0, -1, 0, 0, 0, 0);
    checkLocate(0, 1, 1, 0, 1, 4, 5);
    checkLocate(0, 2, 1, 0, 0, 4, 2);
    checkLocate(0, 3, 2, 0, 2, 5, 4);
    checkLocate(0, 4, 2, 0, 1, 5, 6);
    checkLocate(0, 5, 2, 0, 0, 5, 3);
    checkLocate(1, 1, -1, 0, 0, 0, 0);
    checkLocate(1, 2, 0, 0, 0, 1, 1);
    checkLocate(1, 3, 2, 1, 2, 2, 4);
    checkLocate(1, 4, 2, 1, 1, 2, 6);
    checkLocate(1, 5, 2, 1, 0, 2, 3);
    checkLocate(2, 2, -1, 0, 0, 0, 0);
    checkLocate(2, 3, 0, 0, 0, 1, 1);
    checkLocate(2, 4, 2, 2, 1, 3, 6);
    checkLocate(2, 5, 2, 2, 0, 3, 3);
    checkLocate(3, 3, -1, 0, 0, 0, 0);
    checkLocate(3, 4, 1, 0, 1, 4, 5);
    checkLocate(3, 5, 1, 0, 0, 4, 2);
    checkLocate(4, 4, -1, 0, 0, 0, 0);
    checkLocate(4, 5, 0, 0, 0, 1, 1);
    checkLocate(5, 5, -1, 0, 0, 0, 0);
    // +-+-+-+-+-+
    // |2    |1|0|
    // +     + +-+
    // |     | |  
    // +   +-+-+  
    // |   |0|    
    // +-+-+-+    
    // |1|0|      
    // + +-+      
    // | |        
    // +-+        
    assert(sub.size == 3);
    assert(sub.is == (vector<int>{-1, 0, 2, 2, 1, 2}));
    assert(sub.isRev == (vector<int>{-1, 0, 1, 2, 2, 1, 2}));
    assert(sub.ls == (vector<int>{1, 0, 0}));
    assert(sub.rs == (vector<int>{2, 2, 5}));
    assert(sub.js == (vector<int>{1, 2, 3, 6}));
    assert(sub.jsRev == (vector<int>{1, 2, 4, 7}));
    assert(sub.us == (vector<int>{0, 1, 4, 5, 2, 3}));
    assert(sub.usRev == (vector<int>{0, 1, 2, 5, 3, 6, 4}));
    assert(sub.sizeL(0) == 1); assert(sub.sizeR(0) == 1);
    assert(sub.sizeL(1) == 1); assert(sub.sizeR(1) == 2);
    assert(sub.sizeL(2) == 3); assert(sub.sizeR(2) == 3);
    assert(sub.sizeR(0, 0) == 1);
    assert(sub.sizeL(0, 0) == 1);
    assert(sub.sizeR(1, 0) == 2);
    assert(sub.sizeL(1, 0) == 1); assert(sub.sizeL(1, 1) == 1);
    assert(sub.sizeR(2, 0) == 3); assert(sub.sizeR(2, 1) == 3); assert(sub.sizeR(2, 2) == 2);
    assert(sub.sizeL(2, 0) == 3); assert(sub.sizeL(2, 1) == 3); assert(sub.sizeL(2, 2) == 2);
    // a     100000000000100
    // ab     10000000000010
    // abb     1000000000000
    // abba     100000000000
    // abbab     10000000000
    //  b         1000100001
    //  bb         100000000
    //  bba         10000000
    //  bbab         1000000
    //   ba            10000
    //   bab            1000
    assert(sub.countOffline<long long>({
      {{0, 1}, 100000000000000LL},
      {{0, 2},  10000000000000LL},
      {{0, 3},   1000000000000LL},
      {{0, 4},    100000000000LL},
      {{0, 5},     10000000000LL},
      {{1, 2},      1000000000LL},
      {{1, 3},       100000000LL},
      {{1, 4},        10000000LL},
      {{1, 5},         1000000LL},
      {{2, 3},          100000LL},
      {{2, 4},           10000LL},
      {{2, 5},            1000LL},
      {{3, 4},             100LL},
      {{3, 5},              10LL},
      {{4, 5},               1LL},
    }, {
      {0, 0}, {0, 1}, {0, 2}, {0, 3}, {0, 4}, {0, 5},
              {1, 1}, {1, 2}, {1, 3}, {1, 4}, {1, 5},
                      {2, 2}, {2, 3}, {2, 4}, {2, 5},
                              {3, 3}, {3, 4}, {3, 5},
                                      {4, 4}, {4, 5},
                                              {5, 5},
    }) == (vector<long long>{
                    0LL,
      100000000000100LL,
      110001000100111LL,
      111002100200112LL,
      211102110210212LL,
      221113111311223LL,
                    0LL,
           1000100001LL,
           2100200002LL,
      100002110210102LL,
      110003111311113LL,
                    0LL,
           1000100001LL,
      100001000110101LL,
      110002000211112LL,
                    0LL,
      100000000000100LL,
      110001000100111LL,
                    0LL,
           1000100001LL,
                    0LL,
    }));
  }
  {
    Substring sub("abbababbab");
    cerr << sub << std::flush;
    // 0                                                  
    // |-ab----- 7                                        
    // |         |-abbab----------------- 10              
    // |         `-bab--------- 8                         
    // |                        `-abbab----------------- 9
    // `-b- 1                                             
    //      |-ab----- 2                                   
    //      |         |-abbab----------------- 3          
    //      |         `-bab-------- 4                     
    //      `-bab--------- 5                              
    //                     `-abbab----------------- 6     
    // 0                                                  
    // |-a- 9                                             
    // |    `-b- 10                                       
    // |         |-abba------------- 13                   
    // |         `-ab----- 11                             
    // |                   `-abbab----------------- 12    
    // `-b- 1                                             
    //      |-a- 2                                        
    //      |    `-b- 3                                   
    //      |         |-abba------------- 6               
    //      |         `-ab----- 4                         
    //      |                   `-abbab----------------- 5
    //      `-ab----- 7                                   
    //                `-abbab----------------- 8          
    // +-+-+-+-+-+-+-+-+-+-+
    // |4        |3  |0|2|1|
    // +         +   + + +-+
    // |         |   | | |  
    // +         +   +-+-+  
    // |         |   |1|    
    // +       +-+-+-+-+    
    // |       |0|2|1|      
    // +       + + +-+      
    // |       | | |        
    // +-+-+-+-+-+-+        
    // |3  |0|2|1|          
    // +   + + +-+          
    // |   | | |            
    // +   +-+-+            
    // |   |1|              
    // +-+-+-+              
    // |2|1|                
    // + +-+                
    // | |                  
    // +-+                  
    assert(sub.size == 5);
    assert(sub.is == (vector<int>{-1, 0, 2, 4, 4, 3, 4, 1, 3, 4, 4}));
    assert(sub.isRev == (vector<int>{-1, 0, 1, 2, 3, 4, 4, 3, 4, 1, 2, 3, 4, 4}));
    assert(sub.ls == (vector<int>{1, 0, 2, 0, 0}));
    assert(sub.rs == (vector<int>{2, 2, 5, 5, 10}));
    assert(sub.js == (vector<int>{1, 2, 3, 4, 6, 11}));
    assert(sub.jsRev == (vector<int>{1, 2, 4, 6, 9, 14}));
    assert(sub.us == (vector<int>{0, 1, 7, 2, 8, 5, 9, 6, 3, 10, 4}));
    assert(sub.usRev == (vector<int>{0, 1, 2, 9, 3, 10, 4, 11, 7, 5, 12, 8, 6, 13}));
    assert(sub.sizeL(0) == 1); assert(sub.sizeR(0) == 1);
    assert(sub.sizeL(1) == 1); assert(sub.sizeR(1) == 2);
    assert(sub.sizeL(2) == 1); assert(sub.sizeR(2) == 2);
    assert(sub.sizeL(3) == 2); assert(sub.sizeR(3) == 3);
    assert(sub.sizeL(4) == 5); assert(sub.sizeR(4) == 5);
    assert(sub.sizeR(0, 0) == 1);
    assert(sub.sizeL(0, 0) == 1);
    assert(sub.sizeR(1, 0) == 2);
    assert(sub.sizeL(1, 0) == 1); assert(sub.sizeL(0, 1) == 1);
    assert(sub.sizeR(2, 0) == 2);
    assert(sub.sizeL(2, 0) == 1); assert(sub.sizeL(2, 1) == 1);
    assert(sub.sizeR(3, 0) == 3); assert(sub.sizeR(3, 1) == 3);
    assert(sub.sizeL(3, 0) == 2); assert(sub.sizeL(3, 1) == 2); assert(sub.sizeL(3, 2) == 2);
    assert(sub.sizeR(4, 0) == 5); assert(sub.sizeR(4, 1) == 5); assert(sub.sizeR(4, 2) == 5); assert(sub.sizeR(4, 3) == 5); assert(sub.sizeR(4, 4) == 3);
    assert(sub.sizeL(4, 0) == 5); assert(sub.sizeL(4, 1) == 5); assert(sub.sizeL(4, 2) == 5); assert(sub.sizeL(4, 3) == 4); assert(sub.sizeL(4, 4) == 4);
  }

  test(string(""));
  test(string("a"));
  test(string("abbab"));
  test(string("babba"));
  test(string("abbababbab"));
  test(string("babbababba"));
  test(string("abracadabra"));
  test(string("sismississippi"));
  test(vector<long long>{-2 * (1LL << 62), 2 * ((1LL << 62) - 1) + 1});
  testAllVectors(0, 1);
  testAllVectors(1, 3);
  testAllVectors(2, 3);
  testAllVectors(3, 5);
  testAllVectors(4, 5);
  testAllVectors(5, 7);
  testAllVectors(6, 7);
  testAllVectors(7, 5);
  testAllVectors(8, 4);
  testAllVectors(9, 4);
  testAllVectors(10, 3);
  testAllVectors(11, 3);
  testAllVectors(12, 2);
  testAllVectors(13, 2);
  testAllVectors(14, 2);
  testAllVectors(15, 2);
  testAllVectors(16, 2);
  testAllVectors(17, 2);
  testAllVectors(18, 2);
  for (int sigma = 1; sigma <= 10; ++sigma) {
    for (int caseId = 0; caseId < 100; ++caseId) {
      vector<long long> cs(sigma);
      for (int a = 0; a < sigma; ++a) {
        cs[a] = rng();
      }
      const int n = rng() % 100;
      vector<long long> as(n);
      for (int u = 0; u < n; ++u) {
        as[u] = cs[rng() % sigma];
      }
      test(as);
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
