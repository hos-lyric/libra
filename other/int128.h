#ifndef LIBRA_OTHER_INT128_H_
#define LIBRA_OTHER_INT128_H_

#include <stdio.h>
#include <iostream>

unsigned __int128 toUInt128(const char *s) {
  unsigned __int128 x = 0;
  for (; *s; ++s) x = x * 10 + (*s - '0');
  return x;
}
__int128 toInt128(const char *s) {
  if (*s == '-') return -toInt128(s + 1);
  __int128 x = 0;
  for (; *s; ++s) x = x * 10 + (*s - '0');
  return x;
}
unsigned __int128 inUInt128() {
  static char buf[40];
  scanf("%s", buf);
  return toUInt128(buf);
}
__int128 inInt128() {
  static char buf[40];
  scanf("%s", buf);
  return toInt128(buf);
}

void out(unsigned __int128 x) {
  static char buf[40];
  int len = 0;
  do { buf[len++] = '0' + static_cast<int>(x % 10); } while (x /= 10);
  for (int i = len; --i >= 0; ) putchar(buf[i]);
}
void out(__int128 x) {
  if (x < 0) {
    putchar('-');
    out(-static_cast<unsigned __int128>(x));
  } else {
    out(static_cast<unsigned __int128>(x));
  }
}
std::ostream &operator<<(std::ostream &os, unsigned __int128 x) {
  static char buf[40];
  int len = 0;
  do { buf[len++] = '0' + static_cast<int>(x % 10); } while (x /= 10);
  for (int i = len; --i >= 0; ) os << buf[i];
  return os;
}
std::ostream &operator<<(std::ostream &os, __int128 x) {
  if (x < 0) {
    os << '-' << -static_cast<unsigned __int128>(x);
  } else {
    os << static_cast<unsigned __int128>(x);
  }
  return os;
}

#endif  // LIBRA_OTHER_INT128_H_
