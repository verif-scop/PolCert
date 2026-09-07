#include <stdio.h>

#define N 4

static int x[N][N] = {
    {1, 2, 3, 4},
    {5, 6, 7, 8},
    {9, 10, 11, 12},
    {13, 14, 15, 16},
};
static int y[N][N];

int main(void) {
  int i, j;

#pragma scop
  x[1][1] = 42;
  for (i = 0; i < N; ++i)
    for (j = 0; j < N; ++j)
      y[i][j] = x[i][j];
#pragma endscop

  printf("%d\n", y[1][1]);
  return 0;
}
