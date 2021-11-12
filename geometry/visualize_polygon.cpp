// N
// X[0] Y[0]
// ...
// X[N-1] Y[N-1]

#include <stdio.h>
#include <algorithm>
#include <vector>

using std::max;
using std::vector;

constexpr int SIZE = 500;
constexpr int MARGIN = 50;
constexpr int RADIUS = 2;

int main() {
  int N;
  scanf("%d", &N);
  vector<double> X(N), Y(N);
  for (int i = 0; i < N; ++i) {
    scanf("%lf%lf", &X[i], &Y[i]);
  }

  auto resX = std::minmax_element(X.begin(), X.end());
  auto resY = std::minmax_element(Y.begin(), Y.end());
  const double minX = *resX.first, maxX = *resX.second;
  const double minY = *resY.first, maxY = *resY.second;
  const double unit = SIZE / max({maxX - minX, maxY - minY, 1.0});
  const double x0 = (minX + maxX) / 2.0;
  const double y0 = (minY + maxY) / 2.0;
  vector<double> xs(N), ys(N);
  for (int i = 0; i < N; ++i) {
    xs[i] = MARGIN + SIZE / 2 + unit * (X[i] - x0);
    ys[i] = MARGIN + SIZE / 2 - unit * (Y[i] - y0);
  }

  printf("<script>function f(){"
         "var c=document.getElementById('id').getContext('2d');"
         "\n");
  for (int i = 0; i < N; ++i) {
    printf("c.fillText('%d',%.1f,%.1f);"
           "c.beginPath();"
           "c.arc(%.1f,%.1f,%d,0,2*Math.PI,false);"
           "c.stroke();"
           "\n",
           i, xs[i], ys[i], xs[i], ys[i], RADIUS);
  }
  for (int i = 0; i < N; ++i) {
    printf("c.beginPath();"
           "c.moveTo(%.1f,%.1f);"
           "c.lineTo(%.1f,%.1f);"
           "c.stroke();"
           "\n",
           xs[i], ys[i], xs[(i + 1) % N], ys[(i + 1) % N]);
  }
  printf("}</script><body onload=\"f()\">"
         "<canvas id=\"id\" width=\"%d\" height=\"%d\" "
         "style=\"border:1px solid\"></canvas>"
         "<p>[%.1f, %.1f] &times; [%.1f, %.1f]</p>"
         "</body>"
         "\n",
         SIZE + 2 * MARGIN, SIZE + 2 * MARGIN, minX, maxX, minY, maxY);

  return 0;
}
