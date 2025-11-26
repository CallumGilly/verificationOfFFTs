#include "../src/minus-omega.h"
#include <complex.h>
#include <stddef.h>
#include <stdlib.h>
void dft(size_t n, complex float (*x_0)[], complex float (*dft)[]) {
  for (size_t x_1 = 0; x_1 < n; x_1++) {
    complex float x_2 = 0;
    for (size_t x_3 = 0; x_3 < n; x_3++) {
      x_2 += ((*x_0)[x_3] * minus_omega(n, (x_3 * x_1)));
    }
    (*dft)[x_1] += x_2;
  }
}
