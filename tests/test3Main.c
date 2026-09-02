#include "../src/minus-omega.h"
#include "./test3.c"
#include <complex.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

void PrinterA(size_t n, size_t m, complex real xs[][m]) {
  for (size_t i = 0; i < n; i++) {
    for (size_t j = 0; j < (m - 1); j++) {
      printf("%f,", creal(xs[i][j]));
    }
    printf("%f\n", creal(xs[i][m - 1]));
  }
}

int main() {
  complex real memor[][3] = {{1, 2, 3}, {4, 5, 6}};

  PrinterA(2, 3, memor);
  printf("Was:\n");

  // Force C to print in stderr the type of memor
  // printf("%d", &memor);
  CMtTest3(&memor);

  printf("Now:\n");
  PrinterA(2, 3, memor);
}
