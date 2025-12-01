#define size 72
#define tsize 15

//#include "../generated/dft.h"
#include "../generated/fft.h"
#include "../generated/transTest.h"
#include "./minus-omega.h"

#include <stdio.h>
#include <stdlib.h>
#include <complex.h>
#include <string.h>
#include <math.h>

void testTranspose();
void testDFTFFT();

int main (void) {
  testDFTFFT();
  //testTranspose();

  return 1;
}


void testTranspose() {
  complex real(*input)[tsize] = malloc(sizeof(*input));
  memset(input, 0, sizeof(*input));

  for (size_t ai = 0; ai < tsize; ai++) {
    (*input)[ai] = (real) ai;
  }

  //void transposeTest(complex real (*inp)[4][2][3][3]);
  transposeTest((complex real (*)[3][5])input);

  printf("Should get 0, 5, 10, 1, 6, 11...\n");
  for (size_t ai = 0; ai < tsize; ai++) {
    printf("At Pos: %zu, Got: %.0f\n", ai, creal((*input)[ai]));
  }

  //printf("\nWith casting to (complex real (*)[3]):\n");
  //for (size_t i = 0; i < 5; i++) {
  //  for (size_t j = 0; j < 3; j++) {
  //    printf("At Pos: (%zu, %zu), Got: %.0f\n", i, j, creal(((complex real (*)[3])input)[i][j]));
  //  }
  //}

  //// ((complex real (*)[3])input)[i][j]) or to ((complex real (*)[5])input)[i][j])

  //printf("\nWith casting to (complex real (*)[5]):\n");
  //for (size_t i = 0; i < 5; i++) {
  //  for (size_t j = 0; j < 3; j++) {
  //    printf("At Pos: (%zu, %zu), Got: %.0f\n", i, j, creal(((complex real (*)[5])input)[i][j]));
  //  }
  //}
}

void testDFTFFT() {
  //sh = (ι 4 ⊗ ι 4) ⊗ (ι 3 ⊗ ι 3)
  complex real(*input)[size] = malloc(sizeof(*input));
  memset(input, 0, sizeof(*input));

  complex real(*fftOutput)[size] = malloc(sizeof(*fftOutput));
  memset(fftOutput, 0, sizeof(*fftOutput));

  complex real(*dftOutput)[size] = malloc(sizeof(*dftOutput));
  memset(dftOutput, 0, sizeof(*dftOutput));

  // Garble input
  for (size_t ai = 0; ai < size; ai++) {
    (*input)[ai] = (real)rand()/(real)((real)RAND_MAX/(400.0f)) + ((real)rand()/(real)((real)RAND_MAX/(400.0f)) * I);
    (*fftOutput)[ai] = (*input)[ai];
  }

  DFT(size, (*input), (*dftOutput));
  fft((complex real (*)[4][2][3][3])fftOutput);

  //double realError = 0;
  //double imagError = 0;

  printf("Index, Input-Real, Input-Imag, DFT-Real, DFT-Imag, FFT-Real, FFT-Imag, DFT-FFT-Diff-Real, DFT-FFT-Diff-Imag\n");
  for (size_t ai = 0; ai < size; ai++) {
    //realError += fabs(creal((*input)[ai]) - creal((*dftOutput)[ai]));
    //imagError += fabs(cimag((*input)[ai]) - cimag((*dftOutput)[ai]));

    printf("%zu, %.20f, %.20f, %.20f, %.20f, %.20f, %.20f, %.20f, %.20f\n",
            ai,
            creal((*input)[ai]),
            cimag((*input)[ai]),
            creal((*dftOutput)[ai]),
            cimag((*dftOutput)[ai]),
            creal((*fftOutput)[ai]),
            cimag((*fftOutput)[ai]),
            fabs(creal((*fftOutput)[ai]) - creal((*dftOutput)[ai])),
            fabs(cimag((*fftOutput)[ai]) - cimag((*dftOutput)[ai]))
           );
  }
}

