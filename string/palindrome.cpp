#include <assert.h>
#include <string.h>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

using std::make_pair;
using std::ostream;
using std::pair;
using std::string;
using std::vector;

// |as| = n ==> |rs| = 2 n + 1
// [i - rs[i], i + rs[i]] is palindrome for $ as[0] $ as[1] $ ... $ as[n-1] $
// as[i, j): palindrome <=> j - i <= rs[i + j]
template <class String> vector<int> manacher(const String &as) {
  const int n = as.size();
  vector<int> rs(2 * n + 1);
  for (int i = 0, j = 0, k; i <= 2 * n; i += k, j -= k) {
    for (; 0 < i - j && i + j < 2 * n &&
           (!((i + j + 1) & 1) || as[(i - j - 1) >> 1] == as[(i + j + 1) >> 1]);
         ++j) {}
    rs[i] = j;
    for (k = 1; k < j && k + rs[i - k] < j; ++k) rs[i + k] = rs[i - k];
  }
  return rs;
}

// f(i, j) should check whether [i, j] (inclusive) is palindromic,
// assuming [i+1, j-1] is palindromic.
// Properties used:
//   rs[i] == i  (mod 2)
//   k + rs[i-k] <  rs[i] ==> rs[i+k] = rs[i-k]
//   k + rs[i-k] >= rs[i] ==> rs[i-k] >= rs[i] - k
// rs[2 * i + 1] = -1 is allowed (meaning [i, i] is not palindromic).
template <class Extend> vector<int> manacher(int n, Extend extend) {
  vector<int> rs(2 * n + 1);
  for (int i = 0, j = 0, k; i <= 2 * n; i += k, j -= k) {
    for (; 0 < i - j && i + j < 2 * n &&
           (j < -1 || !((i + j + 1) & 1) || extend((i - j - 1) >> 1, (i + j + 1) >> 1));
         ++j) {}
    rs[i] = j;
    for (k = 1; k < j && k + rs[i - k] < j; ++k) rs[i + k] = rs[i - k];
  }
  return rs;
}


// TODO: no-undo version (to save memory)

// alphabet is [OFFSET, OFFSET + SIZE), with sentinel (OFFSET - 1)
template <class T, int SIZE, T OFFSET> struct Depam {
  struct Node {
    // ts[pos, pos + len]: prefix/suffix when created
    // fail: longest proper palindromic prefix/suffix
    // quick[a]: longest proper palindromic prefix/suffix followed/preceded by a
    int len, pos, fail;
    int nxt[SIZE], quick[SIZE];
  };

  // nodes[0]: length 0  (also means null in nxt)
  // nodes[1]: length -1
  // nodes[2, nodesLen): non-empty palindromic substring
  int nodesLen, pre, suf;
  vector<Node> nodes;
  // current whole string: ts[l, r)  (-nL <= l <= 0 <= r <= nR)
  int nL, nR, l, r;
  vector<T> tsBuffer;
  T *ts;
  // ((~pre)/suf before pushFront/pushBack, parent of created node or -1)
  int historyLen;
  vector<pair<int, int>> history;

  Depam(int nL_, int nR_) : nL(nL_), nR(nR_) {
    nodesLen = 2;
    pre = suf = 0;
    nodes.resize(2 + nL + nR);
    nodes[0].len =  0; nodes[0].pos = 0; nodes[0].fail = 1;
    nodes[1].len = -1; nodes[1].pos = 0; nodes[1].fail = 1;
    memset(nodes[0].nxt, 0, sizeof(nodes[0].nxt));
    memset(nodes[1].nxt, 0, sizeof(nodes[1].nxt));
    for (int a = 0; a < SIZE; ++a) nodes[0].quick[a] = 1;
    for (int a = 0; a < SIZE; ++a) nodes[1].quick[a] = 1;
    l = r = 0;
    tsBuffer.assign(1 + nL + nR + 1, OFFSET - 1);
    ts = tsBuffer.data() + (1 + nL);
    historyLen = 0;
    history.resize(nL + nR);
  }
  const Node &operator[](int u) const {
    return nodes[u];
  }

  void pushFront(T t) {
    assert(-nL < l);
    const int a = t - OFFSET;
    history[historyLen++] = make_pair(~pre, -1);
    ts[--l] = t;
    if (ts[l + 1 + nodes[pre].len] != t) pre = nodes[pre].quick[a];
    Node &f = nodes[pre];
    if (!f.nxt[a]) {
      history[historyLen - 1].second = pre;
      Node &g = nodes[nodesLen];
      g.len = f.len + 2; g.pos = l; g.fail = nodes[f.quick[a]].nxt[a];
      memset(g.nxt, 0, sizeof(g.nxt));
      memcpy(g.quick, nodes[g.fail].quick, sizeof(g.quick));
      g.quick[ts[l + nodes[g.fail].len] - OFFSET] = g.fail;
      f.nxt[a] = nodesLen++;  // this needs to be after setting g.fail
    }
    if (nodes[pre = f.nxt[a]].len == r - l) suf = pre;
  }
  void pushBack(T t) {
    assert(r < nR);
    const int a = t - OFFSET;
    history[historyLen++] = make_pair(suf, -1);
    ts[r++] = t;
    if (ts[r - 2 - nodes[suf].len] != t) suf = nodes[suf].quick[a];
    Node &f = nodes[suf];
    if (!f.nxt[a]) {
      history[historyLen - 1].second = suf;
      Node &g = nodes[nodesLen];
      g.len = f.len + 2; g.pos = r - g.len; g.fail = nodes[f.quick[a]].nxt[a];
      memset(g.nxt, 0, sizeof(g.nxt));
      memcpy(g.quick, nodes[g.fail].quick, sizeof(g.quick));
      g.quick[ts[r - 1 - nodes[g.fail].len] - OFFSET] = g.fail;
      f.nxt[a] = nodesLen++;  // this needs to be after setting g.fail
    }
    if (nodes[suf = f.nxt[a]].len == r - l) pre = suf;
  }
  void undo() {
    const pair<int, int> h = history[--historyLen];
    if (h.first < 0) {
      // pushFront
      if (nodes[pre].len == r - l) suf = nodes[suf].fail;
      pre = ~h.first;
      if (~h.second) {
        --nodesLen;
        nodes[h.second].nxt[ts[l] - OFFSET] = 0;
      }
      ts[l++] = OFFSET - 1;
    } else {
      // pushBack
      if (nodes[suf].len == r - l) pre = nodes[pre].fail;
      suf = h.first;
      if (~h.second) {
        --nodesLen;
        nodes[h.second].nxt[ts[r - 1] - OFFSET] = 0;
      }
      ts[--r] = OFFSET - 1;
    }
  }

  void dfsPrint(ostream &os, int u, const string &branch, int type) const {
    const Node &f = nodes[u];
    os << branch << ((type == 0) ? "" : (type == 1) ? "|-- " : "`-- ");
    if (f.len <= 0) {
      os << "(" << f.len << ")";
    } else {
      for (int i = f.pos; i < f.pos + f.len; ++i) os << ts[i];
    }
    os << " " << u << " " << f.fail;
    // debug here
    os << "\n";
    int a0 = -1;
    for (int a = 0; a < SIZE; ++a) if (f.nxt[a]) a0 = a;
    for (int a = 0; a < SIZE; ++a) if (f.nxt[a]) {
      dfsPrint(os, f.nxt[a],
               branch + ((type == 0) ? "" : (type == 1) ? "|   " : "    "),
               (a == a0) ? 2 : 1);
    }
  }
  friend ostream &operator<<(ostream &os, const Depam &depam) {
    depam.dfsPrint(os, 0, "  ", 0);
    depam.dfsPrint(os, 1, "", 0);
    return os;
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <set>
#include <sstream>

using std::cerr;
using std::endl;
using std::ostringstream;
using std::set;

unsigned xrand() {
  static unsigned x = 314159265, y = 358979323, z = 846264338, w = 327950288;
  unsigned t = x ^ x << 11; x = y; y = z; z = w; return w = w ^ w >> 19 ^ t ^ t >> 8;
}

int unittest_manacher_dfs(int n, int pos, vector<int> &rs) {
  int numCases = 0;
  if (pos == 2 * n + 1) {
    if ([&]() -> bool {
      for (int i = 0; i <= 2 * n; ++i) {
        for (int k = 1; k < rs[i]; ++k) {
          if (k + rs[i - k] <  rs[i] && !(rs[i + k] == rs[i - k])) return false;
          if (k + rs[i - k] >= rs[i] && !(rs[i + k] >= rs[i] - k)) return false;
        }
      }
      return true;
    }()) {
      assert(manacher(n, [&](int i, int j) -> bool {
        assert(i <= j);
        return (j - i + 1 <= rs[i + j + 1]);
      }) == rs);
      numCases += 1;
    }
  } else {
    for (int &r = rs[pos] = -(pos & 1); r <= pos && r <= 2 * n - pos; r += 2) {
      numCases += unittest_manacher_dfs(n, pos + 1, rs);
    }
  }
  return numCases;
}
void unittest_manacher() {
  assert(manacher(string("sismississippi")) == (vector<int>{
  //    s   i   s   m   i   s   s   i   s   s   i   p   p   i  
      0,1,0,3,0,1,0,1,0,1,0,1,4,1,0,7,0,1,4,1,0,1,0,1,4,1,0,1,0}));
  for (int n = 0; n <= 9; ++n) {
    for (int p = 0; p < 1 << (2 * n); ++p) {
      string s(n, '?');
      for (int i = 0; i < n; ++i) s[i] = '0' + (p >> (2 * i) & 3);
      vector<vector<int>> isPalin(n + 1, vector<int>(n + 1, 0));
      for (int i = n; i >= 0; --i) for (int j = i; j <= n; ++j) {
        isPalin[i][j] = (j - i <= 1 || (s[i] == s[j - 1] && isPalin[i + 1][j - 1])) ? 1 : 0;
      }
      vector<int> expected(2 * n + 1, 0);
      for (int i = 0; i <= n; ++i) for (int j = i; j <= n; ++j) if (isPalin[i][j]) {
        if (expected[i + j] < j - i) expected[i + j] = j - i;
      }
      const auto actual = manacher(s);
      assert(expected == actual);
    }
  }
  for (int n = 0; n <= 8; ++n) {
    vector<int> rs(2 * n + 1);
    const int numCases = unittest_manacher_dfs(n, 0, rs);
    cerr << "[unittest_manacher] n = " << n << ": " << numCases << " cases" << endl;
  }
}

void unittest_Depam() {
  // sismississippi
  {
    Depam<char, 26, 'a'> depam(14, 0);
    depam.pushFront('i');
    depam.pushFront('p');
    depam.pushFront('p');
    depam.pushFront('i');
    depam.pushFront('s');
    depam.pushFront('s');
    depam.pushFront('i');
    depam.pushFront('s');
    depam.pushFront('s');
    depam.pushFront('i');
    depam.pushFront('m');
    depam.pushFront('s');
    depam.pushFront('i');
    depam.pushFront('s');
    ostringstream oss;
    oss << depam;
    assert(oss.str() == string(R"(
  (0) 0 1
  |-- pp 4 3
  |   `-- ippi 5 2
  `-- ss 7 6
      `-- issi 8 2
(-1) 1 1
|-- i 2 0
|   `-- sis 9 6
|       `-- ssiss 10 7
|           `-- ississi 11 8
|-- m 12 0
|-- p 3 0
`-- s 6 0
)").substr(1));
  }
  {
    Depam<char, 26, 'a'> depam(0, 14);
    depam.pushBack('s');
    depam.pushBack('i');
    depam.pushBack('s');
    depam.pushBack('m');
    depam.pushBack('i');
    depam.pushBack('s');
    depam.pushBack('s');
    depam.pushBack('i');
    depam.pushBack('s');
    depam.pushBack('s');
    depam.pushBack('i');
    depam.pushBack('p');
    depam.pushBack('p');
    depam.pushBack('i');
    ostringstream oss;
    oss << depam;
    assert(oss.str() == string(R"(
  (0) 0 1
  |-- pp 11 10
  |   `-- ippi 12 3
  `-- ss 6 2
      `-- issi 7 3
(-1) 1 1
|-- i 3 0
|   `-- sis 4 2
|       `-- ssiss 8 6
|           `-- ississi 9 7
|-- m 5 0
|-- p 10 0
`-- s 2 0
)").substr(1));
  }
  {
    Depam<char, 26, 'a'> depam(8, 6);
    depam.pushFront('i');  //        i|
    depam.pushBack('s');   //        i|s
    depam.pushBack('s');   //        i|ss
    depam.pushFront('s');  //       si|ss
    depam.pushFront('s');  //      ssi|ss
    depam.pushBack('i');   //      ssi|ssi
    depam.pushFront('i');  //     issi|ssi
    depam.pushFront('m');  //    missi|ssi
    depam.pushFront('s');  //   smissi|ssi
    depam.pushBack('p');   //   smissi|ssip
    depam.pushFront('i');  //  ismissi|ssip
    depam.pushFront('s');  // sismissi|ssip
    depam.pushBack('p');   // sismissi|ssipp
    depam.pushBack('i');   // sismissi|ssippi
    ostringstream oss;
    oss << depam;
    assert(oss.str() == string(R"(
  (0) 0 1
  |-- pp 11 10
  |   `-- ippi 12 2
  `-- ss 4 3
      `-- issi 7 2
(-1) 1 1
|-- i 2 0
|   `-- sis 5 3
|       `-- ssiss 6 4
|           `-- ississi 8 7
|-- m 9 0
|-- p 10 0
`-- s 3 0
)").substr(1));
  }
  {
    Depam<int, 3, 0> depam(4, 3);
    depam.pushFront(0);  //    0|
    depam.pushBack(0);   //    0|0
    depam.pushFront(1);  //   10|0
    depam.pushFront(2);  //  210|0
    depam.pushBack(2);   //  210|02
    depam.pushFront(1);  // 1210|02
    {
      ostringstream oss;
      oss << depam;
      assert(oss.str() == string(R"(
  (0) 0 1
  `-- 00 3 2
(-1) 1 1
|-- 0 2 0
|-- 1 4 0
`-- 2 5 0
    `-- 121 6 4
)").substr(1));
    }
    depam.undo();        //  210|02
    depam.undo();        //  210|0
    depam.undo();        //   10|0
    {
      ostringstream oss;
      oss << depam;
      assert(oss.str() == string(R"(
  (0) 0 1
  `-- 00 3 2
(-1) 1 1
|-- 0 2 0
`-- 1 4 0
)").substr(1));
    }
    depam.pushBack(1);   //   10|01
    depam.pushBack(0);   //   10|010
    depam.pushFront(0);  //  010|010
    {
      ostringstream oss;
      oss << depam;
      assert(oss.str() == string(R"(
  (0) 0 1
  `-- 00 3 2
      `-- 1001 5 4
          `-- 010010 7 6
(-1) 1 1
|-- 0 2 0
`-- 1 4 0
    `-- 010 6 2
)").substr(1));
    }
  }
  {
    constexpr int NUM_CASES = 100;
    constexpr int NUM_QUERIES = 100;
    for (int caseId = 0; caseId < NUM_CASES; ++caseId) {
      vector<int> ops;
      string s;
      Depam<char, 2, '0'> depam(NUM_QUERIES, NUM_QUERIES);
      for (int q = 0; q < NUM_QUERIES; ++q) {
        if (ops.empty() || xrand() % 3 < 2) {
          const char t = '0' + xrand() % 2;
          const int op = xrand() % 2;
          ops.push_back(op);
          if (op == 0) {
            s = t + s;
            depam.pushFront(t);
          } else {
            s = s + t;
            depam.pushBack(t);
          }
          
        } else {
          assert(!s.empty());
          if (ops.back() == 0) {
            s = s.substr(1);
          } else {
            s = s.substr(0, s.size() - 1);
          }
          ops.pop_back();
          depam.undo();
        }
        const int sLen = s.size();
        auto isPal = [&](int i, int j) -> bool {
          assert(0 <= i); assert(i <= j); assert(j <= sLen);
          for (; i < j; ++i, --j) if (s[i] != s[j - 1]) return false;
          return true;
        };
        for (int u = 2; u < depam.nodesLen; ++u) {
          const auto &f = depam.nodes[u];
          assert(isPal(f.pos - depam.l, f.pos + f.len - depam.l));
        }
        set<string> pals;
        for (int i = 0; i < sLen; ++i) for (int j = i + 1; j <= sLen; ++j) {
          if (isPal(i, j)) {
            pals.insert(s.substr(i, j - i));
          }
        }
        assert(depam.nodesLen == 2 + static_cast<int>(pals.size()));
      }
    }
  }
}

int main() {
  unittest_manacher(); cerr << "PASSED unittest_manacher" << endl;
  unittest_Depam(); cerr << "PASSED unittest_Depam" << endl;
  return 0;
}
