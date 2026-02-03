#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <algorithm>
#include <bitset>
#include <chrono>
#include <complex>
#include <deque>
#include <functional>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include <exception>
#include <thread>

using namespace std;

using Int = long long;

template <class T1, class T2> ostream &operator<<(ostream &os, const pair<T1, T2> &a) { return os << "(" << a.first << ", " << a.second << ")"; };
template <class T> ostream &operator<<(ostream &os, const vector<T> &as) { const int sz = as.size(); os << "["; for (int i = 0; i < sz; ++i) { if (i >= 256) { os << ", ..."; break; } if (i > 0) { os << ", "; } os << as[i]; } return os << "]"; }
template <class T> void pv(T a, T b) { for (T i = a; i != b; ++i) cerr << *i << " "; cerr << endl; }
template <class T> bool chmin(T &t, const T &f) { if (t > f) { t = f; return true; } return false; }
template <class T> bool chmax(T &t, const T &f) { if (t < f) { t = f; return true; } return false; }
#define COLOR(s) ("\x1b[" s "m")



struct Solver {
  int caseId;
  thread thread_;
  Solver() {}
  explicit Solver(int caseId_) : caseId(caseId_) {}
  void start() {
    thread_ = thread(&Solver::main, this);
  }
  void join() {
    thread_.join();
  }
  void main() {
    try {
      run();
      fprintf(stderr, "%sDONE  Case #%d\n%s", COLOR("92"), caseId, COLOR());
      fflush(stderr);
    } catch (exception &e) {
      fprintf(stderr, "%sERROR Case #%d: %s\n%s", COLOR("91"), caseId, e.what(), COLOR());
      fflush(stderr);
    }
  }
  
  
  
  void input() {
    
  }
  
  void run() {
    
  }
  
  void output() {
    printf("Case #%d: \n", caseId);
    fflush(stdout);
  }
};

int main(int argc, char **argv) {
  
  
  for (int numCases; ~scanf("%d", &numCases); ) {
    if (1 < argc) {
      const int numThreads = atoi(argv[1]);
      for (int caseIdL = 1, caseIdR; caseIdL <= numCases; caseIdL = caseIdR) {
        caseIdR = min(caseIdL + numThreads, numCases + 1);
        fprintf(stderr, "%sPARALLEL Case #[%d, %d]\n%s", COLOR("93"), caseIdL, caseIdR - 1, COLOR());
        fflush(stderr);
        vector<Solver> solvers(caseIdR - caseIdL);
        for (int caseId = caseIdL; caseId < caseIdR; ++caseId) {
          solvers[caseId - caseIdL] = Solver(caseId);
        }
        for (auto &solver : solvers) { solver.input(); solver.start(); }
        for (auto &solver : solvers) { solver.join(); solver.output(); }
      }
    } else {
      for (int caseId = 1; caseId <= numCases; ++caseId) {
        Solver solver(caseId);
        solver.input();
        solver.main();
        solver.output();
      }
    }
  }
  return 0;
}
