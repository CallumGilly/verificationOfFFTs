#include <complex.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdio.h>
#include "../src/minus-omega.h"
void dft(size_t n, complex float x_0[], complex float dft[]);

#define DFT(n, xs, ys) \
  { \
    for (size_t i = 0; i < n; i++) { \
      for (size_t j = 0; j < n; j++) { \
        ys[i] += (xs[j] * minus_omega(n, (j * i))); \
      } \
    } \
  }

#define split_dft(n, xs, ys) \
  { \
    for (size_t i = 0; i < n; i++) { \
      for (size_t j = 0; j < n; j++) { \
        ys[0][i] += xs[0][j] * minus_omega_r(n, (j * i)); \
        ys[0][i] -= xs[1][j] * minus_omega_i(n, (j * i)); \
        ys[1][i] += xs[0][j] * minus_omega_i(n, (j * i)); \
        ys[1][i] += xs[1][j] * minus_omega_r(n, (j * i)); \
      } \
    } \
  }

#define split_lane_dft(n, xs, ys) \
  { \
    for (size_t i = 0; i < n; i++) { \
      for (size_t j = 0; j < n; j++) { \
        ys[0][i] += xs[0][j] * minus_omega_r(n, (j * i)); \
        ys[0][i] -= xs[1][j] * minus_omega_i(n, (j * i)); \
        ys[1][i] += xs[0][j] * minus_omega_i(n, (j * i)); \
        ys[1][i] += xs[1][j] * minus_omega_r(n, (j * i)); \
      } \
    } \
  }
