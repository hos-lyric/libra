#include <assert.h>
#include <vector>

using std::vector;

// op: T * T -> T, associative
template <class T, class Op> struct Queue {
  const Op op;
  vector<T> as, aas, bs, bbs;

  Queue(Op op_) : op(op_) {}

  void reserve(int n) {
    as.reserve(n);
    aas.reserve(n);
    bs.reserve(n);
    bbs.reserve(n);
  }
  void reduce() {
    for (; !bs.empty(); bs.pop_back(), bbs.pop_back()) {
      as.push_back(bs.back());
      aas.push_back(aas.empty() ? bs.back() : op(bs.back(), aas.back()));
    }
  }
  T get() {
    if (as.empty()) reduce();
    assert(!as.empty());
    return bbs.empty() ? aas.back() : op(aas.back(), bbs.back());
  }

  bool empty() const {
    return (as.empty() && bs.empty());
  }
  int size() const {
    return as.size() + bs.size();
  }
  T front() {
    if (as.empty()) reduce();
    assert(!as.empty());
    return as.back();
  }
  void push(const T &t) {
    bs.push_back(t);
    bbs.push_back(bbs.empty() ? t : op(bbs.back(), t));
  }
  void pop() {
    if (as.empty()) reduce();
    assert(!as.empty());
    as.pop_back();
    aas.pop_back();
  }
  void clear() {
    as.clear();
    aas.clear();
    bs.clear();
    bbs.clear();
  }
};

////////////////////////////////////////////////////////////////////////////////

#include <iostream>
#include <string>

using std::cerr;
using std::endl;
using std::string;

string cat(const string &a, const string &b) {
  return a + b;
}

void unittest() {
  Queue<string, decltype(&cat)> que(cat);
  que.reserve(1);
  assert(que.size() == 0); assert(que.empty());
  que.push("0");
  assert(que.size() == 1); assert(!que.empty()); assert(que.front() == "0"); assert(que.get() == "0");
  que.pop();
  assert(que.size() == 0); assert(que.empty());
  que.push("1");
  assert(que.size() == 1); assert(!que.empty()); assert(que.front() == "1"); assert(que.get() == "1");
  que.push("2");
  assert(que.size() == 2); assert(!que.empty()); assert(que.front() == "1"); assert(que.get() == "12");
  que.pop();
  assert(que.size() == 1); assert(!que.empty()); assert(que.front() == "2"); assert(que.get() == "2");
  que.push("3");
  assert(que.size() == 2); assert(!que.empty()); assert(que.front() == "2"); assert(que.get() == "23");
  que.pop();
  assert(que.size() == 1); assert(!que.empty()); assert(que.front() == "3"); assert(que.get() == "3");
  que.pop();
  assert(que.size() == 0); assert(que.empty());
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
