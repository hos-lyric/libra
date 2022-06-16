// $ ./int128_test < int128_test.in

#include "int128.h"

#include <assert.h>
#include <stdio.h>
#include <sstream>

#define UMAX_STR "340282366920938463463374607431768211455"
#define MIN_STR "-170141183460469231731687303715884105728"
#define MAX_STR "170141183460469231731687303715884105727"

void unittest() {
  constexpr unsigned __int128 UMAX = -static_cast<unsigned __int128>(1);
  constexpr __int128 MAX = ((static_cast<__int128>(1) << 126) - 1) << 1 | 1;
  constexpr __int128 MIN = (-MAX) - 1;

  // toUInt128
  assert(toUInt128("0") == 0);
  assert(toUInt128(UMAX_STR) == UMAX);
  assert(toUInt128("15241578780673678515622620750190521") ==
         static_cast<unsigned __int128>(123456789123456789ULL) * 123456789123456789ULL);
  // toInt128
  assert(toInt128(MIN_STR) == MIN);
  assert(toInt128("-1") == -1);
  assert(toInt128("0") == 0);
  assert(toInt128(MAX_STR) == MAX);
  assert(toInt128("-55022095598232072031397857488187881") ==
         static_cast<__int128>(-234567891234567891LL) * 234567891234567891LL);
  // inUInt128
  assert(inUInt128() == 0);
  assert(inUInt128() == UMAX);
  assert(inUInt128() ==
         static_cast<unsigned __int128>(345678912345678912ULL) * 345678912345678912ULL);
  // inInt128
  assert(inInt128() == MIN);
  assert(inInt128() == -1);
  assert(inInt128() == 0);
  assert(inInt128() == MAX);
  assert(inInt128() ==
         static_cast<__int128>(-456789123456789123LL) * 456789123456789123LL);

  // out
  puts("0");
  out(static_cast<unsigned __int128>(0));
  puts("");
  puts(UMAX_STR);
  out(UMAX);
  puts("");
  puts("322500454299043663630585965654042756");
  out(static_cast<unsigned __int128>(567891234567891234ULL) * 567891234567891234ULL);
  puts("");
  puts("");
  puts(MIN_STR);
  out(static_cast<__int128>(MIN));
  puts("");
  puts("-1");
  out(static_cast<__int128>(-1));
  puts("");
  puts("0");
  out(static_cast<__int128>(0));
  puts("");
  puts(MAX_STR);
  out(static_cast<__int128>(MAX));
  puts("");
  puts("-460921973115242969847720022193399025");
  out(static_cast<__int128>(-678912345678912345LL) * 678912345678912345LL);
  puts("");
  puts("");
  // operator<<
  {
    std::ostringstream oss;
    oss << static_cast<unsigned __int128>(0) << " "
        << UMAX << " "
        << (static_cast<unsigned __int128>(789123456789123456ULL) * 789123456789123456ULL);
    assert(oss.str() ==
           "0" " "
           UMAX_STR " "
           "622715830054815594241483700809383936");
  }
  {
    std::ostringstream oss;
    oss << MIN << " "
        << static_cast<__int128>(-1) << " "
        << static_cast<__int128>(0) << " "
        << MAX << " "
        << (static_cast<__int128>(-891234567891234567LL) * 891234567891234567LL);
    assert(oss.str() ==
           MIN_STR " "
           "-1" " "
           "0" " "
           MAX_STR " "
           "-794299055004275596625654031415677489");
  }
}

int main() {
  unittest();
  return 0;
}
