#include <assert.h>
#include "nimber.h"

void unittest() {
  using nim::mul;
  assert(mul(0ULL, 0ULL) == 0ULL);
  assert(mul(0ULL, 1ULL) == 0ULL);
  assert(mul(1ULL, 0ULL) == 0ULL);
  assert(mul(1ULL, 1ULL) == 1ULL);
  assert(mul(5ULL, 8ULL) == 3ULL);
  assert(mul(3141ULL, 5926ULL) == 14994ULL);
  assert(mul(18446744073709551615ULL, 18446744073709551615ULL) == 11290409524105353207ULL);
  assert(mul(1ULL << 32, 1ULL << 32) == 3ULL << 31);
  assert(mul(1234567890123456789ULL, 9876543210987654321ULL) == 18059132706730210235ULL);
}

int main() {
  unittest();
  return 0;
}
