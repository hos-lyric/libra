import std.conv, std.functional, std.range, std.stdio, std.string;
import std.algorithm, std.array, std.bigint, std.bitmanip, std.complex, std.container, std.math, std.mathspecial, std.numeric, std.regex, std.typecons;
import core.bitop;
import core.thread;

class EOFException : Throwable { this() { super("EOF"); } }
string[] tokens;
string readToken() { for (; tokens.empty; ) { if (stdin.eof) { throw new EOFException; } tokens = readln.split; } auto token = tokens.front; tokens.popFront; return token; }
int readInt() { return readToken.to!int; }
long readLong() { return readToken.to!long; }

string COLOR(string s = "") { return "\x1b[" ~ s ~ "m"; }

bool chmin(T)(ref T t, in T f) { if (t > f) { t = f; return true; } else { return false; } }
bool chmax(T)(ref T t, in T f) { if (t < f) { t = f; return true; } else { return false; } }

int binarySearch(alias pred, T)(in T[] as) { int lo = -1, hi = cast(int)(as.length); for (; lo + 1 < hi; ) { const mid = (lo + hi) >> 1; (unaryFun!pred(as[mid]) ? hi : lo) = mid; } return hi; }
int lowerBound(T)(in T[] as, T val) { return as.binarySearch!(a => (a >= val)); }
int upperBound(T)(in T[] as, T val) { return as.binarySearch!(a => (a > val)); }




class Solver : core.thread.Thread {
  int caseId;
  this(int caseId_) {
    caseId = caseId_;
    super(&main);
  }
  void main() {
    try {
      run;
      stderr.writefln("DONE  Case #%s", caseId);
    } catch (Throwable e) {
      stderr.writefln("ERROR Case #%s: %s", caseId, e.msg);
    } finally {
      stderr.flush;
    }
  }
  
  
  
  void input() {
    
  }
  
  void run() {
    
  }
  
  void output() {
    stdout.writefln("Case #%s: ", caseId);
    stdout.flush;
  }
}

void main(string[] args) {
  
  
  const numCases = readInt;
  if (1 < args.length) {
    const numThreads = args[1].to!int;
    for (int caseIdL = 1, caseIdR; caseIdL <= numCases; caseIdL = caseIdR) {
      caseIdR = min(caseIdL + numThreads, numCases + 1);
      stderr.writefln("PARALLEL Case #[%s, %s]", caseIdL, caseIdR - 1);
      stderr.flush;
      auto solvers = new Solver[caseIdR - caseIdL];
      foreach (caseId; caseIdL .. caseIdR) {
        solvers[caseId - caseIdL] = new Solver(caseId);
      }
      foreach (solver; solvers) { solver.input; solver.start; }
      foreach (solver; solvers) { solver.join; solver.output; }
    }
  } else {
    foreach (caseId; 1 .. numCases + 1) {
      auto solver = new Solver(caseId);
      solver.input;
      solver.main;
      solver.output;
    }
  }
}
