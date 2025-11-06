#define size 192

#include <stdio.h>
#include <stdlib.h>
#include <complex.h>
#include <string.h>

void main (void) {

  //sh = (ι 4 ⊗ ι 4) ⊗ (ι 3 ⊗ ι 4)
  complex float(*input)[size] = malloc(sizeof(*input));
  memset(input, 0, sizeof(*input));

  complex float(*fftOutput)[size] = malloc(sizeof(*fftOutput));
  memset(fftOutput, 0, sizeof(*fftOutput));

  complex float(*dftOutput)[size] = malloc(sizeof(*dftOutput));
  memset(dftOutput, 0, sizeof(*dftOutput));

  // Garble input
  for (size_t ai = 0; ai < size; ai++) {
    (*input)[ai] = (float)rand()/(float)(RAND_MAX/(400.0f)) + ((float)rand()/(float)(RAND_MAX/(400.0f)) * I);
  }

  fft(*input, *fftOutput);
  dft(*input, *dftOutput);

  float realError = 0;
  float imagError = 0;

  for (size_t ai = 0; ai < size; ai++) {
    realError += fabs(creal((*fftOutput)[ai]) - creal((*dftOutput)[ai]));
    imagError += fabs(cimag((*fftOutput)[ai]) - cimag((*dftOutput)[ai]));
    printf("output[%u] - Real error: %.60f\n", ai, fabs(creal((*fftOutput)[ai]) - creal((*dftOutput)[ai])));
    printf("output[%u] - Imag error: %.60f\n", ai, fabs(cimag((*fftOutput)[ai]) - cimag((*dftOutput)[ai])));
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
