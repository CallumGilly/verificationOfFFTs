#include "../src/minus-omega.h"
#include "./test1.c"
#include <complex.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

#define n 2
#define m 3

void Printer(complex real (*xs)[m]) {
  for (size_t i = 0; i < n; i++) {
    for (size_t j = 0; j < m; j++) {
      printf("%f,", creal(xs[i][j]));
    }
    printf("\n");
  }
}

int main() {
  complex real memor[n][m] = {{1, 2, 3}, {4, 5, 6}};
  printf("Was:\n");
  Printer(memor);
  // CMtTest(&memor);
  // printf("Now:\n");
  // Printer(memor);
}
