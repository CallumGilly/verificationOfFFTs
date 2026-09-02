#include "../src/minus-omega.h"
#include <complex.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
void CMtTest(complex real (*x_0)[2][2]) {
  // Start: copyOut
  complex real(*x_1)[2][2] =
      (complex real(*)[2][2])calloc(4, sizeof(complex real));
  // Copy from (*x_0)[β][β] into x_1 performing eq as we go
  // Shape of (*x_0)[β][β] "is" [2][2]
  // Shape of x_1 "is" [2][2]
  // Loop with x_2 < 2, x_3 < 2,  which becomes x_2 < 2, x_3 < 2,
  for (size_t x_2 = 0; x_2 < 2; x_2++) {
    for (size_t x_3 = 0; x_3 < 2; x_3++) {
      x_1 = (*x_0)[x_2][x_3];
    }
  }
  // Start: imap
  for (size_t x_4 = 0; x_4 < 2; x_4++) {
    for (size_t x_5 = 0; x_5 < 2; x_5++) {
      (*x_1)[x_4][x_5] = (*x_1)[x_4][x_5];
    }
  }
  // End: imap
  //  Copy from x_1 into (*x_0)[β][β] performing ((((up eq) ⊕ (up eq)) ∙ (unflat
  //  ∙ flat)) ∙ ((down eq) ⊕ (down eq))) as we go Shape of x_1 "is" [2][2]
  //  Shape of (*x_0)[β][β] should be cast to [2][2]
  //  Loop with x_6 < 2, x_7 < 2,  which becomes (((2 * x_6) + x_7) / 2) < 2,
  //  (((2 * x_6) + x_7) % 2) < 2, OR Loop with (((2 * x_8) + x_9) / 2) < 2,
  //  (((2 * x_8) + x_9) % 2) < 2,  which becomes x_8 < 2, x_9 < 2,
  for (size_t x_6 = 0; x_6 < 2; x_6++) {
    for (size_t x_7 = 0; x_7 < 2; x_7++) {
      (*x_0)[β][β] = x_1;
    }
  }
  free(x_1);
  // End: copyOut
}
