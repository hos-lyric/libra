#include <assert.h>
#include <iostream>
#include <vector>

using std::cerr;
using std::endl;
using std::ostream;
using std::vector;

template <class T> ostream &operator<<(ostream &os, const vector<T> &as) { const int sz = as.size(); os << "["; for (int i = 0; i < sz; ++i) { if (i >= 256) { os << ", ..."; break; } if (i > 0) { os << ", "; } os << as[i]; } return os << "]"; }

//*
template <class T> struct Vector : vector<T> {
  using vector<T>::vector;
  void checkIndex(long long i) const {
    const long long sz = this->size();
    if (!(0 <= i && i < sz)) {
      cerr << "[Vector] Bad index " << i << " (size " << sz << ")" << endl;
      cerr << *this << endl;
      assert(false);
    }
  }
  T operator[](long long i) const {
    checkIndex(i);
    return this->at(i);
  }
  T &operator[](long long i) {
    checkIndex(i);
    return this->at(i);
  }
};
#define vector Vector
//*/

int main() {
  cerr << vector<int>(1000) << endl;
  vector<int> a{0, 1, 2, 3};
  a[0] = a[1];
  a[4] = 0;
  return 0;
}
