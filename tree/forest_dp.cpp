#include <assert.h>
#include <vector>

using std::vector;

// (without edge property)
// sub[u]: inside subtree at u, rooted at u
// bus[u]: outside subtree at u, rooted at par[u]
// tot[u]: rooted at u
// T: monoid representing information of a subtree.
//   T::init()  should assign the identity.
//   T::pull(const T &l, const T &r)  should assign the product.
//   T::up(int u)  should attach vertex u to the product of the subtrees.
template <class T> struct ForestDP {
  int n;
  vector<vector<int>> graph;
  vector<int> par;
  vector<T> sub, bus, tot;

  ForestDP() : n(0) {}
  explicit ForestDP(int n_) : n(n_), graph(n_) {}
  void ae(int u, int v) {
    assert(0 <= u); assert(u < n);
    assert(0 <= v); assert(v < n);
    graph[u].push_back(v);
    graph[v].push_back(u);
  }
  void run() {
    par.assign(n, -2);
    sub.resize(n);
    bus.resize(n);
    tot.resize(n);
    for (int u = 0; u < n; ++u) if (par[u] == -2) {
      dfs0(u, -1);
      dfs1(u, -1);
    }
  }
  void dfs0(int u, int p) {
    par[u] = p;
    const int deg = graph[u].size();
    int w = -1;
    for (int j = deg; --j >= 0; ) {
      const int v = graph[u][j];
      if (p != v) {
        dfs0(v, u);
        if (~w) {
          bus[v].pull(sub[v], bus[w]);
        } else {
          bus[v] = sub[v];
        }
        w = v;
      }
    }
    if (~w) {
      sub[u] = bus[w];
    } else {
      sub[u].init();
    }
    sub[u].up(u);
  }
  void dfs1(int u, int p) {
    const int deg = graph[u].size();
    int v = -1;
    for (int j = 0; j < deg; ++j) {
      const int w = graph[u][j];
      if (p != w) {
        if (~v) {
          bus[v].pull(tot[v], bus[w]);
          bus[v].up(u);
          tot[w].pull(tot[v], sub[v]);
          dfs1(v, u);
        } else {
          if (~p) {
            tot[w] = bus[u];
          } else {
            tot[w].init();
          }
        }
        v = w;
      }
    }
    if (~v) {
      bus[v] = tot[v];
      bus[v].up(u);
      tot[u].pull(tot[v], sub[v]);
      dfs1(v, u);
    } else {
      if (~p) {
        tot[u] = bus[u];
      } else {
        tot[u].init();
      }
    }
    tot[u].up(u);
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <string>

using std::cerr;
using std::endl;
using std::string;

struct Data {
  string s;
  Data() : s("default") {}
  void init() {
    s = "";
  }
  void pull(const Data &a, const Data &b) {
    assert(this != &a);
    assert(this != &b);
    s = a.s + b.s;
  }
  void up(int u) {
    s = "(" + std::to_string(u) + s + ")";
  }
};

//         0      12 13  14   15
//    /    |  \      |   / \  | 
//   1     2   3     17 18 19 20
//  /|  / /|\  |              | 
// 4 5 6 7 8 9 10             16
//       |                      
//      11                      
void unittest() {
  ForestDP<Data> f(21);
  f.ae(0, 1);
  f.ae(0, 2);
  f.ae(0, 3);
  f.ae(1, 4);
  f.ae(1, 5);
  f.ae(2, 6);
  f.ae(2, 7);
  f.ae(2, 8);
  f.ae(2, 9);
  f.ae(3, 10);
  f.ae(7, 11);
  f.ae(17, 13);
  f.ae(18, 14);
  f.ae(19, 14);
  f.ae(20, 15);
  f.ae(16, 20);
  f.run();
  for (int u = 0; u < f.n; ++u) cerr << "sub[" << u << "] = " << f.sub[u].s << endl;
  for (int u = 0; u < f.n; ++u) cerr << "bus[" << u << "] = " << f.bus[u].s << endl;
  for (int u = 0; u < f.n; ++u) cerr << "tot[" << u << "] = " << f.tot[u].s << endl;
  assert(f.par == (vector<int>{-1, 0, 0, 0, 1, 1, 2, 2, 2, 2, 3, 7, -1, -1, -1, -1, 20, 13, 14, 14, 15}));
  assert(f.sub[0].s == "(0(1(4)(5))(2(6)(7(11))(8)(9))(3(10)))");
  assert(f.sub[1].s == "(1(4)(5))");
  assert(f.sub[2].s == "(2(6)(7(11))(8)(9))");
  assert(f.sub[3].s == "(3(10))");
  assert(f.sub[4].s == "(4)");
  assert(f.sub[5].s == "(5)");
  assert(f.sub[6].s == "(6)");
  assert(f.sub[7].s == "(7(11))");
  assert(f.sub[8].s == "(8)");
  assert(f.sub[9].s == "(9)");
  assert(f.sub[10].s == "(10)");
  assert(f.sub[11].s == "(11)");
  assert(f.sub[12].s == "(12)");
  assert(f.sub[13].s == "(13(17))");
  assert(f.sub[14].s == "(14(18)(19))");
  assert(f.sub[15].s == "(15(20(16)))");
  assert(f.sub[16].s == "(16)");
  assert(f.sub[17].s == "(17)");
  assert(f.sub[18].s == "(18)");
  assert(f.sub[19].s == "(19)");
  assert(f.sub[20].s == "(20(16))");
  assert(f.bus[0].s == "default");
  assert(f.bus[1].s == "(0(2(6)(7(11))(8)(9))(3(10)))");
  assert(f.bus[2].s == "(0(1(4)(5))(3(10)))");
  assert(f.bus[3].s == "(0(1(4)(5))(2(6)(7(11))(8)(9)))");
  assert(f.bus[4].s == "(1(0(2(6)(7(11))(8)(9))(3(10)))(5))");
  assert(f.bus[5].s == "(1(0(2(6)(7(11))(8)(9))(3(10)))(4))");
  assert(f.bus[6].s == "(2(0(1(4)(5))(3(10)))(7(11))(8)(9))");
  assert(f.bus[7].s == "(2(0(1(4)(5))(3(10)))(6)(8)(9))");
  assert(f.bus[8].s == "(2(0(1(4)(5))(3(10)))(6)(7(11))(9))");
  assert(f.bus[9].s == "(2(0(1(4)(5))(3(10)))(6)(7(11))(8))");
  assert(f.bus[10].s == "(3(0(1(4)(5))(2(6)(7(11))(8)(9))))");
  assert(f.bus[11].s == "(7(2(0(1(4)(5))(3(10)))(6)(8)(9)))");
  assert(f.bus[12].s == "default");
  assert(f.bus[13].s == "default");
  assert(f.bus[14].s == "default");
  assert(f.bus[15].s == "default");
  assert(f.bus[16].s == "(20(15))");
  assert(f.bus[17].s == "(13)");
  assert(f.bus[18].s == "(14(19))");
  assert(f.bus[19].s == "(14(18))");
  assert(f.bus[20].s == "(15)");
  assert(f.tot[0].s == "(0(1(4)(5))(2(6)(7(11))(8)(9))(3(10)))");
  assert(f.tot[1].s == "(1(0(2(6)(7(11))(8)(9))(3(10)))(4)(5))");
  assert(f.tot[2].s == "(2(0(1(4)(5))(3(10)))(6)(7(11))(8)(9))");
  assert(f.tot[3].s == "(3(0(1(4)(5))(2(6)(7(11))(8)(9)))(10))");
  assert(f.tot[4].s == "(4(1(0(2(6)(7(11))(8)(9))(3(10)))(5)))");
  assert(f.tot[5].s == "(5(1(0(2(6)(7(11))(8)(9))(3(10)))(4)))");
  assert(f.tot[6].s == "(6(2(0(1(4)(5))(3(10)))(7(11))(8)(9)))");
  assert(f.tot[7].s == "(7(2(0(1(4)(5))(3(10)))(6)(8)(9))(11))");
  assert(f.tot[8].s == "(8(2(0(1(4)(5))(3(10)))(6)(7(11))(9)))");
  assert(f.tot[9].s == "(9(2(0(1(4)(5))(3(10)))(6)(7(11))(8)))");
  assert(f.tot[10].s == "(10(3(0(1(4)(5))(2(6)(7(11))(8)(9)))))");
  assert(f.tot[11].s == "(11(7(2(0(1(4)(5))(3(10)))(6)(8)(9))))");
  assert(f.tot[12].s == "(12)");
  assert(f.tot[13].s == "(13(17))");
  assert(f.tot[14].s == "(14(18)(19))");
  assert(f.tot[15].s == "(15(20(16)))");
  assert(f.tot[16].s == "(16(20(15)))");
  assert(f.tot[17].s == "(17(13))");
  assert(f.tot[18].s == "(18(14(19)))");
  assert(f.tot[19].s == "(19(14(18)))");
  assert(f.tot[20].s == "(20(15)(16))");
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
