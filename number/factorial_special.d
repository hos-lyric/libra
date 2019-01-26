import std.conv, std.regex, std.stdio, std.string;

long[] calc(long m, long k) {
  long[] ret = [1];
  long prod = 1;
  foreach (i; 1 .. (m - 1) / k + 1) {
    foreach (n; k * (i - 1) + 1 .. k * i + 1) {
      (prod *= n) %= m;
    }
    ret ~= prod;
  }
  return ret;
}

void main() {
  foreach (x; [7, 9]) {
    foreach (e; [6, 7]) {
      writefln("// i -> (10^%s i)! mod (10^9 + %s)", e, x);
      writefln("enum long[] FACTORIAL_1E9P%s_1E%s = %s;", x, e,
               calc(10^^9 + x, 10^^e).to!string.replaceAll(regex(` `), ""));
      writeln();
    }
  }
}
