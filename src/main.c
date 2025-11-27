#define size 144

//#include "../generated/dft.h"
#include "../generated/fft.h"

#include <stdio.h>
#include <stdlib.h>
#include <complex.h>
#include <string.h>
#include <math.h>

int main (void) {
  //sh = (ι 4 ⊗ ι 4) ⊗ (ι 3 ⊗ ι 3)
  complex float(*input)[size] = malloc(sizeof(*input));
  memset(input, 0, sizeof(*input));

  complex float(*fftOutput)[size] = malloc(sizeof(*fftOutput));
  memset(fftOutput, 0, sizeof(*fftOutput));

  complex float(*dftOutput)[size] = malloc(sizeof(*dftOutput));
  memset(dftOutput, 0, sizeof(*dftOutput));

  // Garble input
  printf("complex float input[%u] = {\n", size);
  for (size_t ai = 0; ai < size; ai++) {
    (*input)[ai] = (float)rand()/(float)((float)RAND_MAX/(400.0f)) + ((float)rand()/(float)((float)RAND_MAX/(400.0f)) * I);
    printf("%.20f, %.20f\n", creal((*input)[ai]), cimag((*input)[ai]));
  }
  printf("};\n");



  DFT(size, (*input), (*dftOutput));
  fft((complex float (*)[4][2][3][3])input);

  double realError = 0;
  double imagError = 0;

  for (size_t ai = 0; ai < size; ai++) {
    realError += fabs(creal((*input)[ai]) - creal((*dftOutput)[ai]));
    imagError += fabs(cimag((*input)[ai]) - cimag((*dftOutput)[ai]));
    printf("output[%lu] - DFT Real  : %.60f\n", ai, (creal((*dftOutput)[ai])));
    printf("output[%lu] - FFT Real  : %.60f\n", ai, (creal((*input)[ai])));
    printf("output[%lu] - DFT Imag  : %.60f\n", ai, (cimag((*dftOutput)[ai])));
    printf("output[%lu] - FFT Imag  : %.60f\n", ai, (cimag((*input)[ai])));
    printf("output[%lu] - Real error: %.60f\n", ai, fabs(creal((*input)[ai]) - creal((*dftOutput)[ai])));
    printf("output[%lu] - Imag error: %.60f\n", ai, fabs(cimag((*input)[ai]) - cimag((*dftOutput)[ai])));
  }
  printf("\n\n\nAverage Real Error = %.60f\nAverage Imag Error = %.60f\n", (realError / (float) size), (imagError / (float) size));


  // for (size_t ai = 0; ai < size - 1; ai++) {
  //     printf("%.2f+%.2fi, ", creal((*input)[ai]), cimag((*input)[ai]));
  // }
  // printf("%.2f+%.2fi", creal((*input)[size - 1]), cimag((*input)[size - 1]));

  // printf("\n");
  // printf("\n");

  // for (size_t ai = 0; ai < size - 1; ai++) {
  //     printf("%.2f+%.2fi, ", creal((*fftOutput)[ai]), cimag((*fftOutput)[ai]));
  // }
  // printf("%.2f+%.2fi", creal((*fftOutput)[size - 1]), cimag((*fftOutput)[size - 1]));

  // printf("\n");
  // printf("\n");

  // for (size_t ai = 0; ai < size - 1; ai++) {
  //     printf("%.2f+%.2fi, ", creal((*dftOutput)[ai]), cimag((*dftOutput)[ai]));
  // }
  // printf("%.2f+%.2fi", creal((*dftOutput)[size - 1]), cimag((*dftOutput)[size - 1]));
}
