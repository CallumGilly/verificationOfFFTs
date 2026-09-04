#include "../src/minus-omega.h"
#include <complex.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
void CMtTest5(complex real (*x_0)[2][3][4]) {
  // Start: copyOut
  complex real(*x_1)[2][3][4] =
      (complex real(*)[2][3][4])calloc(24, sizeof(complex real));
  // eq
  for (size_t x_2 = 0; x_2 < 2; x_2++) {
    for (size_t x_3 = 0; x_3 < 3; x_3++) {
      for (size_t x_4 = 0; x_4 < 4; x_4++) {
        (*x_1)[x_2][x_3][x_4] = (*x_0)[x_2][x_3][x_4];
      }
    }
  }
  // Start: imap
  for (size_t x_5 = 0; x_5 < 2; x_5++) {
    for (size_t x_6 = 0; x_6 < 3; x_6++) {
      for (size_t x_7 = 0; x_7 < 4; x_7++) {
        (*x_1)[x_5][x_6][x_7] = (*x_1)[x_5][x_6][x_7];
      }
    }
  }
  // End: imap
  //  eq
  for (size_t x_8 = 0; x_8 < 2; x_8++) {
    for (size_t x_9 = 0; x_9 < 3; x_9++) {
      for (size_t x_10 = 0; x_10 < 4; x_10++) {
        (*x_0)[x_8][x_9][x_10] = (*x_1)[x_8][x_9][x_10];
      }
    }
  }
  free(x_1);
  // End: copyOut
}
