// op: T * T -> T, associative
struct Queue(T, alias op) {
  import std.functional : binaryFun;
  alias opFun = binaryFun!op;

  int asLen, bsLen;
  T[] as, aas, bs, bbs;

  this(int n) {
    asLen = bsLen = 0;
    reserve(n);
  }
  void reserve(int n) {
    assert(asLen + bsLen <= n);
    as.length = aas.length = bs.length = bbs.length = n;
  }
  void reduce() {
    for (; bsLen != 0; ++asLen, --bsLen) {
      as[asLen] = bs[bsLen - 1];
      aas[asLen] = (asLen == 0) ? bs[bsLen - 1] : opFun(bs[bsLen - 1], aas[asLen - 1]);
    }
  }
  int size() const {
    return asLen + bsLen;
  }
  void push(T t) {
    insertBack(t);
  }
  void pop() {
    removeFront();
  }
  T get() {
    if (asLen == 0) reduce();
    assert(asLen != 0);
    return (bsLen == 0) ? aas[asLen - 1] : opFun(aas[asLen - 1], bbs[bsLen - 1]);
  }

  bool empty() const {
    return (asLen == 0 && bsLen == 0);
  }
  void clear() {
    asLen = bsLen = 0;
  }
  T front() {
    if (asLen == 0) reduce();
    assert(asLen != 0);
    return as[asLen - 1];
  }
  void insertBack(T t) {
    bs[bsLen] = t;
    bbs[bsLen] = (bsLen == 0) ? t : opFun(bbs[bsLen - 1], t);
    ++bsLen;
  }
  void removeFront() {
    if (asLen == 0) reduce();
    assert(asLen != 0);
    --asLen;
  }
}

////////////////////////////////////////////////////////////////////////////////

unittest {
  auto que = Queue!(string, "a ~ b")(4);
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

void main() {
}
