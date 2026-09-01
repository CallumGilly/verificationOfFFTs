#include "../src/minus-omega.h"
#include <complex.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#ifndef fftn_SIZE
#define fftn_SIZE 4
typedef complex real (*fftn_TYPE)[2];
#endif
void fftn(complex real (*x_0)[2]) {
  // Start: copyOut
  complex real(*x_1)[2] = (complex real(*)[2])calloc(4, sizeof(complex real));
  for (size_t x_2 = 0; x_2 < 2; x_2++) {
    for (size_t x_3 = 0; x_3 < 2; x_3++) {
      x_1[x_2][x_3] = x_0[x_2][x_3];
    }
  }

  // Start: copyOut
  complex real(*x_4)[2] = (complex real(*)[2])calloc(4, sizeof(complex real));
  for (size_t x_5 = 0; x_5 < 2; x_5++) {
    for (size_t x_6 = 0; x_6 < 2; x_6++) {
      x_4[x_5][x_6] = x_1[x_6][x_5];
    }
  }

  // Start: compose
  // Start: compose
  // Start: part
  for (size_t x_7 = 0; x_7 < 2; x_7++) {
    // Start: mapSum
    complex real(*x_8) = (complex real(*))calloc(2, sizeof(complex real));
    for (size_t x_10 = 0; x_10 < 2; x_10++) {
      for (size_t x_9 = 0; x_9 < 2; x_9++) {
        x_8[x_9] += (x_4[x_7][x_10] * (minus_omega(2, (x_10 * x_9))));
      }
    }
    for (size_t x_11 = 0; x_11 < 2; x_11++) {
      x_4[x_7][x_11] = x_8[x_11];
    }
    // End: mapSum
  }
  // End: part
  // Middle: compose
  // Start: imap
  for (size_t x_12 = 0; x_12 < 2; x_12++) {
    for (size_t x_13 = 0; x_13 < 2; x_13++) {
      x_4[x_12][x_13] = (x_4[x_12][x_13] * (minus_omega(4, (x_12 * x_13))));
    }
  }
  // End: imap
  // End: compose
  // Middle: compose
  // Start: part
  for (size_t x_14 = 0; x_14 < 2; x_14++) {
    // Start: mapSum
    complex real(*x_15) = (complex real(*))calloc(2, sizeof(complex real));
    for (size_t x_17 = 0; x_17 < 2; x_17++) {
      for (size_t x_16 = 0; x_16 < 2; x_16++) {
        x_15[x_16] += (x_4[x_17][x_14] * (minus_omega(2, (x_17 * x_16))));
      }
    }
    for (size_t x_18 = 0; x_18 < 2; x_18++) {
      x_4[x_18][x_14] = x_15[x_18];
    }
    // End: mapSum
  }
  // End: part
  // End: compose
  x_1 = (complex real(*)[2])x_4;
  // for (size_t x_20 = 0; x_20 < 2; x_20++) {
  //   for (size_t x_21 = 0; x_21 < 2; x_21++) {
  //     x_1[(((2 * x_20) + x_21) % 2)][(((2 * x_20) + x_21) / 2)] =
  //         x_19[x_20][x_21];
  //   }
  // }
  //  End: copyOut
  complex real(*x_22)[2] = (complex real(*)[2])x_1;
  for (size_t x_23 = 0; x_23 < 2; x_23++) {
    for (size_t x_24 = 0; x_24 < 2; x_24++) {
      x_0[x_23][x_24] = x_22[x_23][x_24];
    }
  }
  // End: copyOut
}
