#include "assert.h"
#include <iostream>
#include <vector>

using std::cerr;
using std::endl;
using std::vector;

//*
template <class T> struct Vector : vector<T> {
  using vector<T>::vector;
  void checkIndex(long long i) const {
    const long long sz = this->size();
    if (!(0 <= i && i < sz)) {
      cerr << "[Vector] Bad index " << i << " (size " << sz << ")" << endl;
      for (long long j = 0; j < sz; ++j) {
        if (j >= 256) {
          cerr << "...";
          break;
        }
        cerr << this->at(j) << " ";
      }
      cerr << endl;
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
  vector<int> a{0, 1, 2, 3};
  a[0] = a[1];
  return 0;
}
