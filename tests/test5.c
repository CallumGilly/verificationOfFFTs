#include "../src/minus-omega.h"
#include <complex.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
void CMtTest5(complex real (*x_0)[2][3]) {
  // Start: copyOut
  complex real(*x_1)[2][3] =
      (complex real(*)[2][3])calloc(6, sizeof(complex real));
  // eq
  for (size_t x_2 = 0; x_2 < 2; x_2++) {
    for (size_t x_3 = 0; x_3 < 3; x_3++) {
      (*x_1)[x_2][x_3] = (*x_0)[x_2][x_3];
    }
  }
  // Start: imap
  for (size_t x_4 = 0; x_4 < 2; x_4++) {
    for (size_t x_5 = 0; x_5 < 3; x_5++) {
      (*x_1)[x_4][x_5] = (*x_1)[x_4][x_5];
    }
  }
  // End: imap
  //  eq
  for (size_t x_6 = 0; x_6 < 2; x_6++) {
    for (size_t x_7 = 0; x_7 < 3; x_7++) {
      (*x_0)[x_6][x_7] = (*x_1)[x_6][x_7];
    }
  }
  free(x_1);
  // End: copyOut
}
