#include "minus-omega.h"
#include <complex.h>
#include <math.h>
#include <stddef.h>
#include <stdio.h>


complex float minus_omega(size_t n, size_t k) {
    //-ω N k = e^i (((-ᵣ (2 ᵣ)) *ᵣ π *ᵣ (k ᵣ)) /ᵣ (N ᵣ))
    complex float result = (complex float) cexp((complex float) (-2.0f * I * M_PI * ((double) k)) / ((double) n));
    printf("minus-omega(%zu, %zu) = %.2f+%.2fi\n", n, k, creal(result), cimag(result));
    return result;
}
