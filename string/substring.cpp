#include "suffix_array.h"

// TODO: !!!topological order!!!

#include <assert.h>
#include <algorithm>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

using std::ostream;
using std::min;
using std::max;
using std::pair;
using std::string;
using std::vector;

// 0 <= u < n: suffix [u, n)
//      n    : root (empty string)
// n <= u < m: LCA needed
struct SuffixTree {
  int n, m, rt;
  SuffixArray sa;
  struct Node {
    int par, len, occ;
    inline int l() const { return occ; }
    inline int r() const { return occ + len; }
  };
  vector<Node> nodes;
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
    stack[0] = rt = n;
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
  }
  const Node &operator[](int u) const {
    return nodes[u];
  }
  // old u -> new perm[u]
  void reindex(const vector<int> &perm) {
    assert(static_cast<int>(perm.size()) == m);
    vector<int> freq(m, 0);
    for (int u = 0; u < m; ++u) assert(++freq[u] == 1);
    rt = perm[rt];
    vector<Node> nodesReindexed(m);
    for (int u = 0; u < m; ++u) {
      Node &node = nodesReindexed[perm[u]] = nodes[u];
      if (~node.par) node.par = perm[node.par];
    }
    nodes.swap(nodesReindexed);
  }

  vector<vector<int>> graph;
  int zeit;
  vector<int> sz, dis, head, sid;
  void dfsSz(int u) {
    sz[u] = 1;
    for (const int v : graph[u]) {
      dfsSz(v);
      sz[u] += sz[v];
    }
  }
  void dfsHld(int u) {
    dis[u] = zeit++;
    const int deg = graph[u].size();
    if (deg > 0) {
      int vm = graph[u][0];
      int jm = 0;
      for (int j = 1; j < deg; ++j) {
        const int v = graph[u][j];
        if (sz[vm] < sz[v]) {
          vm = v;
          jm = j;
        }
      }
      swap(graph[u][0], graph[u][jm]);
      head[vm] = head[u];
      dfsHld(vm);
      for (int j = 1; j < deg; ++j) {
        const int v = graph[u][j];
        head[v] = v;
        dfsHld(v);
      }
    }
  }
  void hld() {
    graph.assign(m, {});
    for (int u = 0; u < m; ++u) if (u != rt) graph[nodes[u].par].push_back(u);
    sz.assign(m, 0);
    dfsSz(rt);
    zeit = 0;
    dis.assign(m, -1);
    head.assign(m, -1);
    head[rt] = rt;
    dfsHld(rt);
    assert(zeit == m);
    sid.assign(m, -1);
    for (int u = 0; u < m; ++u) sid[dis[u]] = u;
  }
  // shallowest node v on rt-u path s.t. nodes[v].len >= len.
  int findUp(int u, int len) const {
    assert(nodes[u].len >= len);
    for (; ; ) {
      const int h = head[u];
      const int p = nodes[h].par;
      if (!~p || nodes[p].len < len) {
        int lo = dis[h] - 1, hi = dis[u];
        for (; lo + 1 < hi; ) {
          const int mid = (lo + hi) / 2;
          ((nodes[sid[mid]].len >= len) ? hi : lo) = mid;
        }
        return sid[hi];
      }
      u = p;
    }
  }
};

struct Substring {
  int n;
  SuffixTree st, stRev;
  // node id of suffix/prefix after reindexed
  vector<int> sufs, pres;
  // representative: [l, r)
  // st   : a, a - 1, ..., a - (sizeL-1)
  // stRev: b, b - 1, ..., b - (sizeR-1)
  struct Block {
    int l, r, sizeL, sizeR, a, b;
  };
  int blocksLen;
  vector<Block> blocks;
  vector<int> blockIds, blockIdsRev;
  Substring() {}
  Substring(const string &str) { build(str); }
  Substring(const vector<int> &str) { build(str); }
  Substring(const vector<long long> &str) { build(str); }
  template <class String> void build(const String &str) {
    n = str.size();
    st = SuffixTree(str, /*lastOcc=*/false);
    auto strRev = str;
    std::reverse(strRev.begin(), strRev.end());
    stRev = SuffixTree(strRev, /*lastOcc=*/true);
    for (int u = 0; u < stRev.m; ++u) stRev.nodes[u].occ = n - stRev.nodes[u].r();
    // radix sort: decr l, incr r
    {
      const int seqLen = (st.m - 1) + (stRev.m - 1);
      vector<int> ptL(n + 1, 0), ptR(n + 1, 0);
      for (int u = 0; u < st.m; ++u) if (u != n) { ++ptL[st[u].l()]; ++ptR[st[u].r()]; }
      for (int u = 0; u < stRev.m; ++u) if (u != n) { ++ptL[stRev[u].l()]; ++ptR[stRev[u].r()]; }
      for (int l = n; l > 0; --l) ptL[l - 1] += ptL[l];
      for (int r = 0; r < n; ++r) ptR[r + 1] += ptR[r];
      vector<int> work(seqLen);
      for (int u = stRev.m; --u >= 0; ) if (u != n) work[--ptR[stRev[u].r()]] = ~u;
      for (int u = st.m; --u >= 0; ) if (u != n) work[--ptR[st[u].r()]] = u;
      vector<int> seq(seqLen);
      for (int i = seqLen; --i >= 0; ) seq[--ptL[(work[i] >= 0) ? st[work[i]].l() : stRev[~work[i]].l()]] = work[i];
      int a = 0, b = 0;
      pres.assign(stRev.m, 0);
      for (int i = 0; i < seqLen; ++i) {
        if (seq[i] < 0) pres[~seq[i]] = ++b;
        if (i >= 1 && seq[i - 1] >= 0 && seq[i] < 0 && st[seq[i - 1]].l() == stRev[~seq[i]].l() && st[seq[i - 1]].r() == stRev[~seq[i]].r()) {
          const int u = seq[i - 1], v = ~seq[i];
          a += (stRev[v].len - stRev[stRev[v].par].len);
          blocks.push_back(Block{
            /*l=*/st[u].l(),
            /*r=*/st[u].r(),
            /*sizeL=*/stRev[v].len - stRev[stRev[v].par].len,
            /*sizeR=*/st[u].len - st[st[u].par].len,
            /*a=*/a,
            /*b=*/b,
          });
        }
      }
    }
    blocksLen = blocks.size();
    // radix sort: incr r, decr l
    {
      const int seqLen = (st.m - 1) + blocksLen;
      vector<int> ptL(n + 1, 0), ptR(n + 1, 0);
      for (int u = 0; u < st.m; ++u) if (u != n) { ++ptL[st[u].l()]; ++ptR[st[u].r()]; }
      for (int k = 0; k < blocksLen; ++k) { ++ptL[blocks[k].l]; ++ptR[blocks[k].r]; }
      for (int l = n; l > 0; --l) ptL[l - 1] += ptL[l];
      for (int r = 0; r < n; ++r) ptR[r + 1] += ptR[r];
      vector<int> work(seqLen);
      for (int k = blocksLen; --k >= 0; ) work[--ptL[blocks[k].l]] = ~k;
      for (int u = st.m; --u >= 0; ) if (u != n) work[--ptL[st[u].l()]] = u;
      vector<int> seq(seqLen);
      for (int i = seqLen; --i >= 0; ) seq[--ptR[(work[i] >= 0) ? st[work[i]].r() : blocks[~work[i]].r]] = work[i];
      sufs.assign(st.m, 0);
      for (int i = 0; i < seqLen; ++i) if (seq[i] < 0) {
        const Block &block = blocks[~seq[i]];
        for (int x = 0; x < block.sizeL; ++x) sufs[seq[i - 1 - x]] = block.a - x;
      }
    }
    st.reindex(sufs);
    st.hld();
    stRev.reindex(pres);
    stRev.hld();
    sufs.resize(n + 1);
    pres.resize(n + 1);
    std::reverse(pres.begin(), pres.end());
    blockIds.assign(st.m, -1);
    blockIdsRev.assign(stRev.m, -1);
    for (int k = 0; k < blocksLen; ++k) {
      for (int x = 0; x < blocks[k].sizeL; ++x) blockIds[blocks[k].a - x] = k;
      for (int y = 0; y < blocks[k].sizeR; ++y) blockIdsRev[blocks[k].b - y] = k;
    }
  }
  friend ostream &operator<<(ostream &os, const Substring &sub) {
    const int width = max(static_cast<int>(std::to_string(max(sub.st.m, sub.stRev.m) - 1).size()) + 1, 3);
    for (int dir = 0; dir < 2; ++dir) {
      for (int r = sub.n; r > 0; --r) {
        for (int l = 0; l < r; ++l) {
          int k;
          string s;
          if (dir == 0) {
            const int u = sub.locate(l, r).first;
            k = sub.blockIds[u];
            if (sub.st[u].len == r - l) s = to_string(u);
          } else {
            const int u = sub.locate(l, r).second;
            k = sub.blockIdsRev[u];
            if (sub.stRev[u].len == r - l) s = to_string(u);
          }
          os << "\x1b[" << (41 + k % 6) << "m";
          os << string(width - static_cast<int>(s.size()), ' ') << s;
          os << "\x1b[m";
        }
        os << '\n';
      }
    }
    return os;
  }
  int sizeR(int k, int x = 0) const {
    assert(0 <= x); assert(x < blocks[k].sizeL);
    const int u = blocks[k].a - x;
    return st[u].len - st[st[u].par].len;
  }
  int sizeL(int k, int y = 0) const {
    assert(0 <= y); assert(y < blocks[k].sizeR);
    const int u = blocks[k].b - y;
    return stRev[u].len - stRev[stRev[u].par].len;
  }
  // shallowest node of st    for [l, r') s.t. r <= r'
  // shallowest node of stRev for [l', r) s.t. l' <= l
  pair<int, int> locate(int l, int r) const {
    assert(0 <= l); assert(l <= r); assert(r <= n);
    return std::make_pair(st.findUp(sufs[l], r - l), stRev.findUp(pres[r], r - l));
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>

using std::cerr;
using std::endl;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

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
  for (int l = n; --l >= 0; ) for (int r = l + 1; r <= n; ++r) {
    if (occss[l][r][0] != l) continue;
    if (l > 0 && occss[l - 1][r].size() == occss[l][r].size()) continue;
    if (r < n && occss[l][r + 1].size() == occss[l][r].size()) continue;
    corners.emplace_back(l, r);
  }

  // SuffixTree
  {
    const SuffixTree st0(as, /*lastOcc=*/false), st1(as, /*lastOcc=*/true);
    const int m = st0.m;
    assert(st0.n == n);
    assert(st1.n == n);
    assert(st0.m == m);
    assert(st1.m == m);
    assert(st0.rt == n);
    assert(st1.rt == n);
    assert(static_cast<int>(st0.nodes.size()) == m);
    assert(static_cast<int>(st1.nodes.size()) == m);
    for (int u = 0; u < m; ++u) {
      if (u == n) {
        assert(st0[u].par == -1);
        assert(st1[u].par == -1);
        assert(st0[u].len == 0);
        assert(st1[u].len == 0);
        assert(st0[u].occ == 0);
        assert(st1[u].occ == n);
      } else {
        const int p = st0[u].par;
        assert(st0[u].par == p);
        assert(st1[u].par == p);
        assert(st0[p].len < st0[u].len);
        assert(st1[p].len < st1[u].len);
        const int len = st0[u].len, occ = st0[u].occ;
        assert(0 <= occ); assert(occ <= occ + len); assert(occ + len <= n);
        const auto occs = occss[occ][occ + len];
        assert(st0[u].len == len);
        assert(st0[u].occ == occs[0]);
        assert(st1[u].len == len);
        assert(st1[u].occ == occs.back());
        assert(st0[u].l() == occs[0]);
        assert(st0[u].r() == occs[0] + len);
        assert(st1[u].l() == occs.back());
        assert(st1[u].r() == occs.back() + len);
      }
    }
  }

  Substring sub(as);
  assert(sub.n == n);
  assert(static_cast<int>(sub.sufs.size()) == n + 1);
  for (int l = 0; l <= n; ++l) {
    const int u = sub.sufs[l];
    assert(0 <= u); assert(u < sub.st.m);
    const SuffixTree::Node &node = sub.st[u];
    assert(node.occ == occss[l][n][0]);
    assert(node.len == n - l);
  }
  assert(static_cast<int>(sub.pres.size()) == n + 1);
  for (int r = 0; r <= n; ++r) {
    const int u = sub.pres[r];
    assert(0 <= u); assert(u < sub.stRev.m);
    const SuffixTree::Node &node = sub.stRev[u];
    assert(node.occ == 0);
    assert(node.len == r);
  }
  assert(static_cast<int>(sub.blockIds.size()) == sub.st.m);
  assert(static_cast<int>(sub.blockIdsRev.size()) == sub.stRev.m);
  assert(sub.blockIds[0] == -1);
  assert(sub.blockIdsRev[0] == -1);
  assert(sub.blocksLen == static_cast<int>(corners.size()));
  for (int k = 0; k < sub.blocksLen; ++k) {
    const int l = corners[k].first, r = corners[k].second;
    vector<int> freqX, freqY;
    for (int x = 0; l + x < r && occss[l + x][r].size() == occss[l][r].size(); ++x) freqX.push_back(0);
    for (int y = 0; l < r - y && occss[l][r - y].size() == occss[l][r].size(); ++y) freqY.push_back(0);
    for (int x = 0; l + x < r && occss[l + x][r].size() == occss[l][r].size(); ++x) {
      for (int y = 0; l + x < r - y && occss[l + x][r - y].size() == occss[l][r].size(); ++y) {
        ++freqX[x];
        ++freqY[y];
      }
    }
    const Substring::Block &block = sub.blocks[k];
    assert(block.l == l);
    assert(block.r == r);
    assert(block.sizeL == static_cast<int>(freqX.size()));
    assert(block.sizeR == static_cast<int>(freqY.size()));
    for (int x = 0; x < block.sizeL; ++x) assert(sub.sizeR(k, x) == freqX[x]);
    for (int y = 0; y < block.sizeR; ++y) assert(sub.sizeL(k, y) == freqY[y]);
    for (int x = 0; x < block.sizeL; ++x) assert(sub.blockIds[block.a - x] == k);
    for (int y = 0; y < block.sizeR; ++y) assert(sub.blockIdsRev[block.b - y] == k);
  }
  // TODO: locate
  for (int l = 0; l <= n; ++l) for (int r = l; r <= n; ++r) {
    int ll = l, rr = r;
    for (; rr < n && occss[l][rr + 1].size() == occss[l][rr].size(); ++rr) {}
    for (; ll > 0 && occss[ll - 1][r].size() == occss[ll][r].size(); --ll) {}
    const auto loc = sub.locate(l, r);
    assert(0 <= loc.first); assert(loc.first < sub.st.m);
    assert(0 <= loc.second); assert(loc.second < sub.stRev.m);
    {
      const SuffixTree::Node &node = sub.st[loc.first];
      assert(node.occ == occss[l][rr][0]);
      assert(node.len == rr - l);
    }
    {
      const SuffixTree::Node &node = sub.stRev[loc.second];
      assert(node.occ == occss[ll][r][0]);
      assert(node.len == r - ll);
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
    // 0                         
    // |-ab----- 2               
    // |         `-bab--------- 5
    // `-b- 1                    
    //      |-ab----- 3          
    //      `-bab--------- 4     
    // 0                         
    // |-a- 2                    
    // |    `-abb--------- 5     
    // `-b- 1                    
    //      |-a- 3               
    //      |    `-abb--------- 6
    //      `-ab------4          
    assert(sub.sufs == (vector<int>{5, 4, 3, 2, 1, 0}));
    assert(sub.pres == (vector<int>{0, 2, 3, 4, 5, 6}));
    assert(sub.locate(0, 0) == std::make_pair(0, 0));
    assert(sub.locate(0, 1) == std::make_pair(2, 2));
    assert(sub.locate(0, 2) == std::make_pair(2, 3));
    assert(sub.locate(0, 3) == std::make_pair(5, 4));
    assert(sub.locate(0, 4) == std::make_pair(5, 5));
    assert(sub.locate(0, 5) == std::make_pair(5, 6));
    assert(sub.locate(1, 1) == std::make_pair(0, 0));
    assert(sub.locate(1, 2) == std::make_pair(1, 1));
    assert(sub.locate(1, 3) == std::make_pair(4, 4));
    assert(sub.locate(1, 4) == std::make_pair(4, 5));
    assert(sub.locate(1, 5) == std::make_pair(4, 6));
    assert(sub.locate(2, 2) == std::make_pair(0, 0));
    assert(sub.locate(2, 3) == std::make_pair(1, 1));
    assert(sub.locate(2, 4) == std::make_pair(3, 5));
    assert(sub.locate(2, 5) == std::make_pair(3, 6));
    assert(sub.locate(3, 3) == std::make_pair(0, 0));
    assert(sub.locate(3, 4) == std::make_pair(2, 2));
    assert(sub.locate(3, 5) == std::make_pair(2, 3));
    assert(sub.locate(4, 4) == std::make_pair(0, 0));
    assert(sub.locate(4, 5) == std::make_pair(1, 1));
    assert(sub.locate(5, 5) == std::make_pair(0, 0));
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
    assert(sub.blocksLen == 3);
    assert(sub.blocks[0].l == 1); assert(sub.blocks[0].r == 2);
    assert(sub.blocks[1].l == 0); assert(sub.blocks[1].r == 2);
    assert(sub.blocks[2].l == 0); assert(sub.blocks[2].r == 5);
    assert(sub.blocks[0].sizeL == 1); assert(sub.blocks[0].sizeR == 1);
    assert(sub.blocks[1].sizeL == 1); assert(sub.blocks[1].sizeR == 2);
    assert(sub.blocks[2].sizeL == 3); assert(sub.blocks[2].sizeR == 3);
    assert(sub.blocks[0].a == 1); assert(sub.blocks[0].b == 1);
    assert(sub.blocks[1].a == 2); assert(sub.blocks[1].b == 3);
    assert(sub.blocks[2].a == 5); assert(sub.blocks[2].b == 6);
    assert(sub.sizeR(0, 0) == 1);
    assert(sub.sizeL(0, 0) == 1);
    assert(sub.sizeR(1, 0) == 2);
    assert(sub.sizeL(1, 0) == 1); assert(sub.sizeL(1, 1) == 1);
    assert(sub.sizeR(2, 0) == 3); assert(sub.sizeR(2, 1) == 3); assert(sub.sizeR(2, 2) == 2);
    assert(sub.sizeL(2, 0) == 3); assert(sub.sizeL(2, 1) == 3); assert(sub.sizeL(2, 2) == 2);
    assert(sub.blockIds == (vector<int>{-1, 0, 1, 2,2,2}));
    assert(sub.blockIdsRev == (vector<int>{-1, 0, 1,1, 2,2,2}));
    cerr << sub << flush;
  }
  {
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
    Substring sub("abbababbab");
    assert(sub.sufs == (vector<int>{10, 9, 8, 7, 6, 5, 4, 1, 3, 2, 0}));
    assert(sub.pres == (vector<int>{0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13}));
    assert(sub.blocksLen == 5);
    assert(sub.blocks[0].l == 2); assert(sub.blocks[0].r == 5);
    assert(sub.blocks[1].l == 1); assert(sub.blocks[1].r == 2);
    assert(sub.blocks[2].l == 0); assert(sub.blocks[2].r == 2);
    assert(sub.blocks[3].l == 0); assert(sub.blocks[3].r == 5);
    assert(sub.blocks[4].l == 0); assert(sub.blocks[4].r == 10);
    assert(sub.blocks[0].sizeL == 1); assert(sub.blocks[0].sizeR == 2);
    assert(sub.blocks[1].sizeL == 1); assert(sub.blocks[1].sizeR == 1);
    assert(sub.blocks[2].sizeL == 1); assert(sub.blocks[2].sizeR == 2);
    assert(sub.blocks[3].sizeL == 2); assert(sub.blocks[3].sizeR == 3);
    assert(sub.blocks[4].sizeL == 5); assert(sub.blocks[4].sizeR == 5);
    assert(sub.blocks[0].a == 1); assert(sub.blocks[0].b == 2);
    assert(sub.blocks[1].a == 2); assert(sub.blocks[1].b == 3);
    assert(sub.blocks[2].a == 3); assert(sub.blocks[2].b == 5);
    assert(sub.blocks[3].a == 5); assert(sub.blocks[3].b == 8);
    assert(sub.blocks[4].a == 10); assert(sub.blocks[4].b == 13);
    assert(sub.sizeR(0, 0) == 2);
    assert(sub.sizeL(0, 0) == 1); assert(sub.sizeL(0, 1) == 1);
    assert(sub.sizeR(1, 0) == 1);
    assert(sub.sizeL(1, 0) == 1);
    assert(sub.sizeR(2, 0) == 2);
    assert(sub.sizeL(2, 0) == 1); assert(sub.sizeL(2, 1) == 1);
    assert(sub.sizeR(3, 0) == 3); assert(sub.sizeR(3, 1) == 3);
    assert(sub.sizeL(3, 0) == 2); assert(sub.sizeL(3, 1) == 2); assert(sub.sizeL(3, 2) == 2);
    assert(sub.sizeR(4, 0) == 5); assert(sub.sizeR(4, 1) == 5); assert(sub.sizeR(4, 2) == 5); assert(sub.sizeR(4, 3) == 5); assert(sub.sizeR(4, 4) == 3);
    assert(sub.sizeL(4, 0) == 5); assert(sub.sizeL(4, 1) == 5); assert(sub.sizeL(4, 2) == 5); assert(sub.sizeL(4, 3) == 4); assert(sub.sizeL(4, 4) == 4);
    assert(sub.blockIds == (vector<int>{-1, 0, 1, 2, 3,3, 4,4,4,4,4}));
    assert(sub.blockIdsRev == (vector<int>{-1, 0,0, 1, 2,2, 3,3,3, 4,4,4,4,4}));
    cerr << sub << flush;
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
        cs[a] = xrand() | static_cast<unsigned long long>(xrand()) << 32;
      }
      const int n = xrand() % 100;
      vector<long long> as(n);
      for (int u = 0; u < n; ++u) {
        as[u] = cs[xrand() % sigma];
      }
      test(as);
    }
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
