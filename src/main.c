#include <stdio.h>
#include <stdlib.h>
#include <complex.h>
#include <string.h>

//void function_name(complex float (x_0)[5][6][7], complex float (X)[7][6][5]);
void fft(complex float (x_0)[2][3][3], complex float (X)[3][3][2]);


void main (void) {

  // complex float (*input)[5][6][7] = malloc(sizeof(*input));
  // memset(input, 0, sizeof(*input));
  // 
  // (*input)[1][1][3] = 3 + I * 2;
  // (*input)[2][6][1] = I * 2;
  // (*input)[3][1][3] = 3 + I * 2;
  // (*input)[3][4][3] = I * 2;
  // (*input)[2][2][7] = I * 2;
  // (*input)[1][1][3] = I * 2;

  // complex float (*output)[7][6][5] = malloc(sizeof(*output));
  // memset(output, 0, sizeof(*output));
  // for (int x_1 = 0; x_1 < 5; x_1++) {
  //   for (int x_2 = 0; x_2 < 6; x_2++) {
  //     for (int x_3 = 0; x_3 < 7; x_3++) {
  //       printf("%.2f+%.2fi, ", creal((*input)[x_1][x_2][x_3]), cimag((*input)[x_1][x_2][x_3]));
  //       //printf("%.2f+%.2fi", creal(), cimag());
  //      }
  //     printf("\n");
  //   }
  //   printf("\n");
  // }

  // printf("\nOutput\n");

  // for (int x_1 = 0; x_1 < 7; x_1++) {
  //   for (int x_2 = 0; x_2 < 6; x_2++) {
  //     for (int x_3 = 0; x_3 < 5; x_3++) {
  //       printf("%.2f+%.2fi, ", creal((*output)[x_1][x_2][x_3]), cimag((*output)[x_1][x_2][x_3]));
  //       //printf("%.2f+%.2fi", creal(), cimag());
  //      }
  //     printf("\n");
  //   }
  //   printf("\n");
  // }

  complex float(*input)[2][3][3] = malloc(sizeof(*input));
  memset(input, 0, sizeof(*input));
  (*input)[0][0][0] = 0 + (0 * I);
  (*input)[0][0][1] = 1 + (0 * I);
  (*input)[0][0][2] = 2 + (0 * I);
  (*input)[0][1][0] = 3 + (0 * I);
  (*input)[0][1][1] = 4 + (0 * I);
  (*input)[0][1][2] = 5 + (0 * I);
  (*input)[0][2][0] = 6 + (0 * I);
  (*input)[0][2][1] = 7 + (0 * I);
  (*input)[0][2][2] = 8 + (0 * I);
  (*input)[1][0][0] = 9 + (0 * I);
  (*input)[1][0][1] = 9 + (0 * I);
  (*input)[1][0][2] = 8 + (0 * I);
  (*input)[1][1][0] = 7 + (0 * I);
  (*input)[1][1][1] = 6 + (0 * I);
  (*input)[1][1][2] = 5 + (0 * I);
  (*input)[1][2][0] = 4 + (0 * I);
  (*input)[1][2][1] = 3 + (0 * I);
  (*input)[1][2][2] = 2 + (0 * I);

  complex float(*output)[3][3][2] = malloc(sizeof(*output));
  memset(output, 0, sizeof(*output));

  fft(*input, *output);

  for (int x_1 = 0; x_1 < 2; x_1++) {
    for (int x_2 = 0; x_2 < 3; x_2++) {
      for (int x_3 = 0; x_3 < 3; x_3++) {
        printf("%.2f+%.2fi, ", creal((*input)[x_1][x_2][x_3]), cimag((*input)[x_1][x_2][x_3]));
        //printf("%.2f+%.2fi", creal(), cimag());
       }
      printf("\n");
    }
    printf("\n");
  }

  printf("\nOutput\n");

  for (int x_1 = 0; x_1 < 3; x_1++) {
    for (int x_2 = 0; x_2 < 3; x_2++) {
      for (int x_3 = 0; x_3 < 2; x_3++) {
        printf("%.2f+%.2fi, ", creal((*output)[x_1][x_2][x_3]), cimag((*output)[x_1][x_2][x_3]));
        //printf("%.2f+%.2fi", creal(), cimag());
       }
      printf("\n");
    }
    printf("\n");
  }

  // printf("Test of complex multiplication:\n");
  // complex float randComplexNumber = CMPLXF(0.31, -0.95);
  // printf("Random Complex number = %.2f+%.2fi\n", creal(randComplexNumber), cimag(randComplexNumber));
  // complex float minusOne = (I * I);
  // printf("Minus One = %.2f+%.2fi\n", creal(minusOne), cimag(minusOne));
  // complex float cplxTimesMinusOne = randComplexNumber * minusOne;
  // printf("Random Complex number * Minus one = %.2f+%.2fi\n", creal(cplxTimesMinusOne), cimag(cplxTimesMinusOne));
  
  //printf("%.2f+%.2fi", creal(n), cimag(n));

}
