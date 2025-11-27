#include "minus-omega.h"
#include <complex.h>
#include <math.h>
#include <stddef.h>
#include <stdio.h>

#define FLOAT_REAL

// If none of these will be defined, "real" will be illegal
#if (defined (FLOAT_REAL))
#define real float
#define cos_real cosf
#define sin_real sinf
#define cexp_real cexpf

#elif (defined (DOUBLE_REAL))
#define real double
#define cos_real cos
#define sin_real sin
#define cexp_real cexp

#endif

complex real minus_omega(size_t n, size_t k) {
 
  // This is something that we can always compute upfront
  real alpha = (real)(-2 * M_PI * (real)k / (real)n);
 
  // Now we can either use sin/cos directly
  //complex real r = cos_real(alpha) + I*sin_real(alpha);

  // Alternatively, we can use cexp, which might behave funny when
  // higher levels of optimisations are on.
  complex real r1 = cexp_real(I*alpha);
 
  //printf("minus-omega(%zu, %zu) = %.2f+%.2fi\n", n, k, creal(r), cimag(r));
  //printf("minus-omega(%zu, %zu) = %.2f+%.2fi\n", n, k, creal(r1), cimag(r1));
  return r1;
}
