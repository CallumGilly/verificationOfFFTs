#include "minus-omega.h"
#include <complex.h>
#include <math.h>


complex float minus_omega(int n, int k) {
    //-ω N k = e^i (((-ᵣ (2 ᵣ)) *ᵣ π *ᵣ (k ᵣ)) /ᵣ (N ᵣ))
    float PI = acos(-1);
    complex float result = cexpf((-2 * I * PI * k) / n);
    //printf("minus-omega(%u, %u) = %.2f+%.2fi\n", n, k, creal(result), cimag(result));
    return result;
}
