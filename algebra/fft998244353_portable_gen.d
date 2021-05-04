import std.range, std.stdio;
void main() {
  enum DELIMITER = '/'.repeat(80).array.idup;
  foreach (filename; ["modint.h", "fft998244353.h", "poly998244353.cpp"]) {
    auto file = File(filename, "r");
    bool inside = false;
    foreach (line; file.byLine) {
      if (line == DELIMITER) {
        inside = !inside;
      }
      if (inside) {
        writeln(line);
      }
    }
    writeln(DELIMITER);
    writeln;
  }
}
