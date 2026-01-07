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

#define SPLIT_DFT(n, xs, ys) \
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

      //ι 0 ≡ (s₁_r * s₁_r) - (s₁_i * s₂_i)
      //ι 1 ≡ (s₁_r * s₂_i) + (s₁_i * s₂_r)
#define COMP_MULT(__a_r, __a_i, __b_r, __b_i, __component) \
    { \
      if ( __component == 0) \
        return (__a_r * __b_r) - (__a_i * __b_i) \
      return (__a_r * __b_i) + (__a_i * __b_r) \
    }

