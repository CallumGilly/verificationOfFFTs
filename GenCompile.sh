./GenCCode.sh && gcc ./src/minus-omega.c ./generated/fft.c ./generated/dft.c ./src/main.c -Wall -Wextra -Wconversion -lm -o program
