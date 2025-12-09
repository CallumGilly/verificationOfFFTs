//#include "../generated/dft.h"
#include "../generated/fft.h"
#include "../generated/transTest.h"
#include "./minus-omega.h"
#include "./dft.h"

#include <stdio.h>
#include <stdlib.h>
#include <complex.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define SIZE 105
#define TSIZE 15

typedef real (*FFT_TYPE)[2][3][5];

void testTranspose();
void testDFTFFT();

int main (void) {
  testDFTFFT();
  //testTranspose();

  return 1;
}


void testTranspose() {
  real(*input)[TSIZE] = malloc(sizeof(*input));
  memset(input, 0, sizeof(*input));

  for (size_t ai = 0; ai < TSIZE; ai++) {
    (*input)[ai] = (real) ai;
  }

  //void transposeTest(complex real (*inp)[4][2][3][3]);
  transposeTest((real (*)[3][5])input);

  printf("Should get 0, 5, 10, 1, 6, 11...\n");
  for (size_t ai = 0; ai < TSIZE; ai++) {
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
  //    printf("At Pos: M(%zu, %zu), Got: %.0f\n", i, j, creal(((complex real (*)[5])input)[i][j]));
  //  }
  //}
}

void testDFTFFT() {
  //sh = (ι 4 ⊗ ι 4) ⊗ (ι 3 ⊗ ι 3)
  complex real(*input)[SIZE] = malloc(sizeof(*input));
  memset(input, 0, sizeof(*input));

  real(*fftMem)[2 * SIZE] = malloc(sizeof(*fftMem));
  memset(fftMem, 0, sizeof(*fftMem));

  complex real(*dftOutput)[SIZE] = malloc(sizeof(*dftOutput));
  memset(dftOutput, 0, sizeof(*dftOutput));

  real(*dftSplitOutput)[2 * SIZE] = malloc(sizeof(*dftSplitOutput));
  memset(dftSplitOutput, 0, sizeof(*dftSplitOutput));

  srand((unsigned int) time(NULL));
  // Garble input
  for (size_t ai = 0; ai < SIZE; ai++) {
    (*fftMem)[ai] = (real)rand()/(real)((real)RAND_MAX/(400.0f));
    (*fftMem)[SIZE + ai] = (real)rand()/(real)((real)RAND_MAX/(400.0f));
    (*input)[ai] = (*fftMem)[ai] + ((*fftMem)[SIZE + ai] * I);
  }

  DFT(SIZE, (*input), (*dftOutput));
  SPLIT_DFT(SIZE, ((real (*)[SIZE])fftMem), ((real (*)[SIZE])dftSplitOutput));
  fft((FFT_TYPE)fftMem);

  //double realError = 0;
  //double imagError = 0;

  printf("Index, Input-Real, Input-Imag, DFT-Real, DFT-Imag, FFT-Real, FFT-Imag, DFT-FFT-Diff-Real, DFT-FFT-Diff-Imag\n");
  for (size_t ai = 0; ai < SIZE; ai++) {
    //realError += fabs(creal((*input)[ai]) - creal((*dftOutput)[ai]));
    //imagError += fabs(cimag((*input)[ai]) - cimag((*dftOutput)[ai]));

    printf("%zu, %.20f, %.20f, %.20f, %.20f, %.20f, %.20f, %.20f, %.20f\n",
            ai,
            creal((*input)[ai]),
            cimag((*input)[ai]),
            ((*dftSplitOutput)[ai]),
            ((*dftSplitOutput)[SIZE + ai]),
            ((*fftMem)[ai]),
            ((*fftMem)[SIZE + ai]),
            fabs(((*fftMem)[ai]) - creal((*dftOutput)[ai])),
            fabs(((*fftMem)[SIZE + ai]) - cimag((*dftOutput)[ai]))
           );
  }
}

