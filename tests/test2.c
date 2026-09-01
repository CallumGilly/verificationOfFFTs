#include "../src/minus-omega.h"
#include <complex.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
void CMtTest2(complex real (*x_0)[3][2]) {
  // Start: copyOut
  complex real(*x_1)[3][2] =
      (complex real(*)[3][2])calloc(6, sizeof(complex real));
  for (size_t x_2 = 0; x_2 < 3; x_2++) {
    for (size_t x_3 = 0; x_3 < 2; x_3++) {
      (*x_1)[x_2][x_3] = (*x_0)[x_2][x_3];
    }
  }

  // Start: imap
  for (size_t x_4 = 0; x_4 < 3; x_4++) {
    for (size_t x_5 = 0; x_5 < 2; x_5++) {
      (*x_1)[x_4][x_5] = (*x_1)[x_4][x_5];
    }
  }
  // End: imap
  //  SOMETHING GOES WRONG HERE:
  //  ((eq ⊕ eq) ∙ ((((up eq) ⊕ (up eq)) ∙ ((((((up eq) ∙ (down eq)) ⊕ ((up eq)
  //  ∙ (down eq))) ∙ unflat) ∙ eq) ∙ (flat ∙ (((up eq) ∙ (down eq)) ⊕ ((up eq)
  //  ∙ (down eq)))))) ∙ ((down eq) ⊕ (down eq))))
  complex real(*x_6)[2][3] = (complex real(*)[2][3])x_1;
  for (size_t x_7 = 0; x_7 < 2; x_7++) {
    for (size_t x_8 = 0; x_8 < 3; x_8++) {
      (*x_0)[(((3 * x_7) + x_8) / 2)][(((3 * x_7) + x_8) % 2)] =
          (*x_6)[x_7][x_8];
    }
  }
  // End: copyOut
}
