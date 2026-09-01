#include "../src/minus-omega.h"
#include "./test1.c"
#include <complex.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

void Printer(size_t n, size_t m, complex real xs[][2]) {
  for (size_t i = 0; i < n; i++) {
    for (size_t j = 0; j < (m - 1); j++) {
      printf("%f,", creal(xs[i][j]));
    }
    printf("%f\n", creal(xs[i][m - 1]));
  }
}

int main() {
  complex real memor[][2] = {{1, 2}, {3, 4}, {5, 6}};
  for (size_t i = 0; i < 3; i++) {
    for (size_t j = 0; j < (2 - 1); j++) {
      printf("%f,", creal(memor[i][j]));
    }
    printf("%f\n", creal(memor[i][2 - 1]));
  }
  printf("Was:\n");
  CMtTest(&memor);

  printf("Now:\n");
  for (size_t i = 0; i < 3; i++) {
    for (size_t j = 0; j < (2 - 1); j++) {
      printf("%f,", creal(memor[i][j]));
    }
    printf("%f\n", creal(memor[i][2 - 1]));
  }
}
