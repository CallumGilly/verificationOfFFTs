#ifndef MINUSOMEGA_H
#define MINUSOMEGA_H


#include <complex.h>
#include <math.h>
#include <stddef.h>

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

complex real minus_omega(size_t n, size_t k);

#endif
