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
    assert(oss.str() == "Graph(n=0; )");
  }
  {
    Graph g;
    g = Graph(0);
    g.build(true);
    ostringstream oss;
    oss << g;
    assert(oss.str() == "Graph(n=0; )");
  }
  {
    Graph g;
    g = Graph(1);
    g.ae(0, 0);
    g.build(false);
    ostringstream oss;
    oss << g;
    assert(oss.str() == "Graph(n=1; 0:[0,0])");
  }
  {
    Graph g;
    g = Graph(1);
    g.ae(0, 0);
    g.build(true);
    ostringstream oss;
    oss << g;
    assert(oss.str() == "Graph(n=1; 0:[0])");
  }
  {
    Graph g;
    g = Graph(8);
    g.ae(3, 0);
    g.ae(5, 5);
    g.ae(6, 0);
    g.ae(4, 7);
    g.ae(4, 5);
    g.ae(4, 7);
    g.ae(0, 1);
    g.build(false);
    ostringstream oss;
    oss << g;
    assert(oss.str() == "Graph(n=8; 0:[3,6,1], 1:[0], 2:[], 3:[0], 4:[7,5,7], 5:[5,5,4], 6:[0], 7:[4,4])");
  }
  {
    Graph g;
    g = Graph(8);
    g.ae(3, 0);
    g.ae(5, 5);
    g.ae(6, 0);
    g.ae(4, 7);
    g.ae(4, 5);
    g.ae(4, 7);
    g.ae(0, 1);
    g.build(true);
    ostringstream oss;
    oss << g;
    assert(oss.str() == "Graph(n=8; 0:[1], 1:[], 2:[], 3:[0], 4:[7,5,7], 5:[5], 6:[0], 7:[])");
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
