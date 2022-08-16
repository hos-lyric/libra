#include "graph.h"

#include <iostream>
#include <sstream>

using std::cerr;
using std::endl;
using std::ostringstream;

void unittest() {
  {
    Graph g;
    g = Graph(0);
    g.build(false);
    ostringstream oss;
    oss << g;
    assert(oss.str() == "Graph(n=0;)");
  }
  {
    Graph g;
    g = Graph(0);
    g.build(true);
    ostringstream oss;
    oss << g;
    assert(oss.str() == "Graph(n=0;)");
  }
  {
    Graph g;
    g = Graph(1);
    g.ae(0, 0);
    g.build(false);
    assert(g.deg(0) == 2);
    ostringstream oss;
    oss << g;
    assert(oss.str() == "Graph(n=1; 0:[0,0])");
  }
  {
    Graph g;
    g = Graph(1);
    g.ae(0, 0);
    g.build(true);
    assert(g.deg(0) == 1);
    ostringstream oss;
    oss << g;
    assert(oss.str() == "Graph(n=1; 0:[0])");
  }
  {
    Graph g;
    g = Graph(8);
    g.ae(3, 0);
    g.ae(5, 5);
    g.ae(0, 6);
    g.ae(4, 7);
    g.ae(4, 5);
    g.ae(4, 7);
    g.ae(0, 1);
    g.build(false);
    assert(g.deg(0) == 3);
    assert(g.deg(1) == 1);
    assert(g.deg(2) == 0);
    assert(g.deg(3) == 1);
    assert(g.deg(4) == 3);
    assert(g.deg(5) == 3);
    assert(g.deg(6) == 1);
    assert(g.deg(7) == 2);
    ostringstream oss;
    oss << g;
    assert(oss.str() == "Graph(n=8; 0:[3,6,1] 1:[0] 2:[] 3:[0] 4:[7,5,7] 5:[5,5,4] 6:[0] 7:[4,4])");
  }
  {
    Graph g;
    g = Graph(8);
    g.ae(3, 0);
    g.ae(5, 5);
    g.ae(0, 6);
    g.ae(4, 7);
    g.ae(4, 5);
    g.ae(4, 7);
    g.ae(0, 1);
    g.build(true);
    assert(g.deg(0) == 2);
    assert(g.deg(1) == 0);
    assert(g.deg(2) == 0);
    assert(g.deg(3) == 1);
    assert(g.deg(4) == 3);
    assert(g.deg(5) == 1);
    assert(g.deg(6) == 0);
    assert(g.deg(7) == 0);
    ostringstream oss;
    oss << g;
    assert(oss.str() == "Graph(n=8; 0:[6,1] 1:[] 2:[] 3:[0] 4:[7,5,7] 5:[5] 6:[] 7:[])");
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
