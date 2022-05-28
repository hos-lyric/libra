#include <assert.h>

////////////////////////////////////////////////////////////////////////////////
// F[x]/(...+x^n)
namespace f2x {

using u32 = unsigned;
using u64 = unsigned long long;
using u128 = unsigned __int128;

// -, x, 1 + x + x^2, 1 + x + x^3, ...
constexpr unsigned IRRED[65] = {0, 0, 3, 3, 3, 5, 3, 3, 27, 3, 9, 5, 9, 27, 33, 3, 43, 9, 9, 39, 9, 5, 3, 33, 27, 9, 27, 39, 3, 5, 3, 9, 141, 75, 27, 5, 53, 63, 99, 17, 57, 9, 39, 89, 33, 27, 3, 33, 45, 113, 29, 75, 9, 71, 125, 71, 149, 17, 99, 123, 3, 39, 105, 3, 27};

template <class T> T mul(int n, T a, T b);
template <> u32 mul<u32>(int n, u32 a, u32 b) {
  // assert(1 <= n); assert(n <= 32);
  u64 c = 0;
  for (int i = 0; i < n; ++i) if (a >> i & 1) c ^= static_cast<u64>(b) << i;
  for (int i = n - 1; --i >= 0; ) if (c >> (n + i) & 1) c ^= static_cast<u64>(IRRED[n]) << i;
  c &= (static_cast<u64>(1) << n) - 1;
  return c;
}
template <> u64 mul<u64>(int n, u64 a, u64 b) {
  // assert(1 <= n); assert(n <= 64);
  u128 c = 0;
  for (int i = 0; i < n; ++i) if (a >> i & 1) c ^= static_cast<u128>(b) << i;
  for (int i = n - 1; --i >= 0; ) if (c >> (n + i) & 1) c ^= static_cast<u128>(IRRED[n]) << i;
  c &= (static_cast<u128>(1) << n) - 1;
  return c;
}

template <class T> T power(int n, T a, unsigned long long e) {
  for (T b = a, c = 1; ; ) {
    if (e & 1) c = mul(n, c, b);
    if (!(e >>= 1)) return c;
    b = mul(n, b, b);
  }
}

template <class T> T inv(int n, T a) {
  assert(a);
  return power(n, a, ((static_cast<T>(1) << (n - 1)) - 1) << 1);
}

}  // namespace f2x

////////////////////////////////////////////////////////////////////////////////

void unittest() {
  using namespace f2x;
  // mul
  {
    assert(mul<u32>(1, 0b1U, 0b1U) == 0b1U);
    assert(mul<u32>(5, 0b10101U, 0b11001U) == 0b11011U);
    assert(mul<u64>(5, 0b10101ULL, 0b11001ULL) == 0b11011ULL);
    assert(mul<u32>(32, 0b10100000'10001010'00101000'10101100U,
                        0b00000010'00000001'00000010'00010011U) ==
                        0b00100011'01010001'10101100'11101001U);
    assert(mul<u64>(32, 0b10100000'10001010'00101000'10101100ULL,
                        0b00000010'00000001'00000010'00010011ULL) ==
                        0b00100011'01010001'10101100'11101001ULL);
    assert(mul<u64>(64,
        0b11010010'00100001'00000100'00001000'00001000'00000100'00000001'00000000ULL,
        0b11100000'00000000'00000000'00000001'10000000'00000000'00000000'00000111ULL) ==
        0b10111001'10101101'00011101'01110110'11011110'11111010'01010101'11111000ULL);
  }
  // power
  for (int n = 1; n <= 9; ++n) {
    for (u32 a = 0; a < 1U << n; ++a) {
      u32 b = 1U;
      for (int e = 0; e < 1 << n; ++e) {
        assert(power<u32>(n, a, e) == b);
        assert(power<u64>(n, a, e) == b);
        b = mul<u32>(n, b, a);
      }
    }
  }
  // inv
  for (int n = 1; n <= 9; ++n) {
    for (u32 a = 1; a < 1U << n; ++a) {
      const u32 b = inv<u32>(n, a);
      assert(mul<u32>(n, a, b) == 1U);
    }
  }
}

int main() {
  unittest();
  return 0;
}
