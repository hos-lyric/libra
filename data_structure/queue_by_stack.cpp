#include <assert.h>
#include <vector>

using std::vector;

template <class T, class PushFront, class PushBack, class Undo>
struct QueueByStack {
  const PushFront pushFront;
  const PushBack pushBack;
  const Undo undo;
  // 0: front, 1: back
  vector<char> dirs;
  vector<T> ls, rs;
  QueueByStack(PushFront pushFront_, PushBack pushBack_, Undo undo_)
      : pushFront(pushFront_), pushBack(pushBack_), undo(undo_) {}
  void push(const T &t) {
    dirs.push_back(1);
    rs.push_back(t);
    pushBack(t);
  }
  void pop() {
    assert(!dirs.empty());
    if (!dirs.back()) {
      dirs.pop_back();
      ls.pop_back();
      undo();
    } else if (ls.empty()) {
      const int rsLen = rs.size();
      dirs.assign(rsLen - 1, 0);
      for (int i = rsLen; --i >= 0; ) undo();
      for (int i = rsLen; --i >= 1; ) {
        ls.push_back(rs[i]);
        pushFront(rs[i]);
      }
      rs.clear();
    } else {
      int lsLen = ls.size(), rsLen = rs.size();
      for (const int keep = lsLen & (lsLen - 1); keep < lsLen; ) {
        dirs.back() ? --rsLen : --lsLen;
        dirs.pop_back();
        undo();
      }
      ls.pop_back();
      for (int i = rsLen; i < static_cast<int>(rs.size()); ++i) {
        dirs.push_back(1);
        pushBack(rs[i]);
      }
      for (int i = lsLen; i < static_cast<int>(ls.size()); ++i) {
        dirs.push_back(0);
        pushFront(ls[i]);
      }
    }
  }
};
template <class T, class PushFront, class PushBack, class Undo>
QueueByStack<T, PushFront, PushBack, Undo>
queueByStack(PushFront pushFront, PushBack pushBack, Undo undo) {
  return QueueByStack<T, PushFront, PushBack, Undo>(pushFront, pushBack, undo);
}

////////////////////////////////////////////////////////////////////////////////

#include <deque>
#include <iostream>

using std::cerr;
using std::deque;
using std::endl;

void unittest_dfs(int n, int pos, int now, int dep, int &counter, vector<int> &ops) {
  if (pos == 2 * n) {
    vector<int> countF(n, 0), countB(n, 0);
    vector<int> history;
    deque<int> expected, actual;
    auto pushFront = [&](int a) -> void {
      ++countF[a];
      history.push_back(0);
      actual.push_front(a);
    };
    auto pushBack = [&](int a) -> void {
      ++countB[a];
      history.push_back(1);
      actual.push_back(a);
    };
    auto undo = [&]() -> void {
      assert(!history.empty());
      history.back() ? actual.pop_back() : actual.pop_front();
      history.pop_back();
    };
    auto que = queueByStack<int>(pushFront, pushBack, undo);
    for (const int a : ops) {
      if (~a) {
        expected.push_back(a);
        que.push(a);
      } else {
        expected.pop_front();
        que.pop();
      }
      assert(expected == actual);
      assert(expected.size() == que.dirs.size());
      assert(expected.size() == que.ls.size() + que.rs.size());
    }
    const int bsr = 31 - __builtin_clz(n);
    for (int a = 0; a < n; ++a) {
      assert(countF[a] <= bsr + 1);
      assert(countB[a] <= bsr + 1);
    }
    ++counter;
  } else {
    if (now < n) {
      ops[pos] = now;
      unittest_dfs(n, pos + 1, now + 1, dep + 1, counter, ops);
    }
    if (dep > 0) {
      ops[pos] = -1;
      unittest_dfs(n, pos + 1, now, dep - 1, counter, ops);
    }
  }
}
void unittest() {
  for (int n = 1; n <= 15; ++n) {
    int counter = 0;
    vector<int> ops(2 * n, -2);
    unittest_dfs(n, 0, 0, 0, counter, ops);
    cerr << "[unittest] DONE n = " << n << ": " << counter << " cases" << endl;
  }
}

int main() {
  unittest(); cerr << "PASSED unittest" << endl;
  return 0;
}
