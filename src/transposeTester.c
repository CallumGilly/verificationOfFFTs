// #include "../generated/FFT.h"
// #include "../generated/transTest.h"
// #include "../generated/fftCube.h"
// #include "./minus-omega.h"
// #include "./dft.h"

#include <stdio.h>
#include <stdlib.h>
#include <complex.h>
#include <string.h>
#include <math.h>
#include <time.h>

int main() {
  int(*x_0)[4] = (int (*)[4])calloc(12, sizeof(int));
  int(*x_1)[4] = (int (*)[4])calloc(12, sizeof(int));

  for (size_t ai = 0; ai < 12; ai++) {
    x_0[ai / 4][ai % 4] = (int) ai;
  }

  for (size_t i = 0; i < 3; i++) {
    for (size_t j = 0; j < 4; j++) {
      printf("%u, ", x_0[i][j]);
    }
    printf("\n");
  }

  for (size_t x_20 = 0; x_20 < 3; x_20++) {
    for (size_t x_21 = 0; x_21 < 4; x_21++) {
      x_1[(((3 * x_20) + x_21) % 4)][(((3 * x_20) + x_21) / 4)] =
          x_0[x_20][x_21];
    }
  }

  printf("\n");
  for (size_t i = 0; i < 3; i++) {
    for (size_t j = 0; j < 4; j++) {
      printf("%u, ", x_1[i][j]);
    }
    printf("\n");
  }
}
