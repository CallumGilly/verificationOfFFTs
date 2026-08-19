//#include "../generated/dft.h"
#include "../generated/FFT.h"
// #include "../generated/transTest.h"
// #include "../generated/fftCube.h"
#include "./minus-omega.h"
#include "./dft.h"

#include <stdio.h>
#include <stdlib.h>
#include <complex.h>
#include <string.h>
#include <math.h>
#include <time.h>

//void testTranspose();
void testDFTFFT();
//void testDFTFFTCUBE();
void printer(size_t n, complex real input[], complex real dftOutput[], complex real fftOutput[]);

/*****************************************************************************/

// FFT Size & Shape
//#define SIZE 384
//typedef real (*FFT_TYPE)[2][4][8][12];

// Transpose Test Size
#define TRANSPOSE_TEST_SIZE 16

int main (void) {
  testDFTFFT();
  //testTranspose();
  //testDFTFFTCUBE();

  return 1;
}

/*****************************************************************************/

/*
void testTranspose() {
  real(*input)[TRANSPOSE_TEST_SIZE] = malloc(sizeof(*input));
  memset(input, 0, sizeof(*input));

  for (size_t ai = 0; ai < TRANSPOSE_TEST_SIZE; ai++) {
    (*input)[ai] = (real) ai;
  }

  transposeTest((real (*)[2][2][2][2])input);

  for (size_t ai = 0; ai < TRANSPOSE_TEST_SIZE; ai++) {
    printf("At Pos: %zu, Got: %.0f\n", ai, creal((*input)[ai]));
  }
}
*/

void testDFTFFT() {
  complex real(*input)[fftn_SIZE] = malloc(sizeof(*input));
  memset(input, 0, sizeof(*input));

  complex real(*fftnMem)[fftn_SIZE] = malloc(sizeof(*fftnMem));
  memset(fftnMem, 0, sizeof(*fftnMem));

  complex real(*dftOutput)[fftn_SIZE] = malloc(sizeof(*dftOutput));
  memset(dftOutput, 0, sizeof(*dftOutput));

  srand((unsigned int) time(NULL));
  // Garble input
  real x_r; real x_i;
  for (size_t ai = 0; ai < fftn_SIZE; ai++) {
    x_r = (real)rand()/(real)((real)RAND_MAX/(400.0f));
    x_i = (real)rand()/(real)((real)RAND_MAX/(400.0f));
    (*input)[ai] = x_r + (x_i * I);
    (*fftnMem)[ai] = x_r + (x_i * I);
  }

  dft(fftn_SIZE, (*input), (*dftOutput));
  // SPLIT_DFT(fftn_SIZE, ((real (*)[fftn_SIZE])splitDftMem), ((real (*)[fftn_SIZE])dftSplitOutput));
  fftn((fftn_TYPE)fftnMem);

  printer(fftn_SIZE, *input, *dftOutput, *fftnMem);
}

/*
void testDFTFFTCUBE() {
  complex real(*input)[FFT_CUBE_SIZE] = malloc(sizeof(*input));
  memset(input, 0, sizeof(*input));

  real(*fftMem)[2 * FFT_CUBE_SIZE] = malloc(sizeof(*fftMem));
  memset(fftMem, 0, sizeof(*fftMem));

  real(*splitDftMem)[2 * FFT_CUBE_SIZE] = malloc(sizeof(*splitDftMem));
  memset(splitDftMem, 0, sizeof(*splitDftMem));

  real(*dftSplitOutput)[2 * FFT_CUBE_SIZE] = malloc(sizeof(*dftSplitOutput));
  memset(dftSplitOutput, 0, sizeof(*dftSplitOutput));

  srand((unsigned int) time(NULL));
  // Garble input
  real x_r; real x_i;
  for (size_t ai = 0; ai < FFT_CUBE_SIZE; ai++) {
    x_r = (real)rand()/(real)((real)RAND_MAX/(400.0f));
    x_i = (real)rand()/(real)((real)RAND_MAX/(400.0f));
    (*input)[ai] = x_r + (x_i * I);
    (*fftMem)[ai] = x_r;
    (*fftMem)[(FFT_CUBE_SIZE + ai)] = x_i;
    (*splitDftMem)[ai] = x_r;
    (*splitDftMem)[FFT_CUBE_SIZE + ai] = x_i;
  }

  SPLIT_DFT(FFT_CUBE_SIZE, ((real (*)[FFT_CUBE_SIZE])splitDftMem), ((real (*)[FFT_CUBE_SIZE])dftSplitOutput));
  fftCube((FFT_CUBE_TYPE)fftMem);

  printer(FFT_CUBE_SIZE, *input, *dftSplitOutput, *fftMem);
}
*/

void printer(size_t n, complex real input[], complex real dftOutput[], complex real fftOutput[]) {

  printf("Index, Input-Real, Input-Imag, DFT-Real, DFT-Imag, FFT-Real, FFT-Imag, DFT-FFT-Diff-Real, DFT-FFT-Diff-Imag\n");
  for (size_t ai = 0; ai < n; ai++) {
    printf("%zu, %.20f, %.20f, %.20f, %.20f, %.20f, %.20f, %.20f, %.20f\n",
            ai,
            creal((input)[ai]),
            cimag((input)[ai]),
            creal((dftOutput)[ai    ]),
            cimag((dftOutput)[ai    ]),
            creal((fftOutput)[ai    ]),
            cimag((fftOutput)[ai    ]),
            fabs(creal((fftOutput)[ai]) - creal((dftOutput)[ai])),
            fabs(cimag((fftOutput)[ai]) - cimag((dftOutput)[ai]))
           );
  }


}
