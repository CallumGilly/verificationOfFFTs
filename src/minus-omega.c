#include "minus-omega.h"
#include <complex.h>
#include <math.h>
#include <stddef.h>


complex float minus_omega(size_t n, size_t k) {
    //-ω N k = e^i (((-ᵣ (2 ᵣ)) *ᵣ π *ᵣ (k ᵣ)) /ᵣ (N ᵣ))
    complex float result = cexpf((float) (-2 * I * M_PI * ((float) k)) / ((float) n));
    //printf("minus-omega(%u, %u) = %.2f+%.2fi\n", n, k, creal(result), cimag(result));
    return result;
}
