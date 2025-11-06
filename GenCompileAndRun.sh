./GenCCode.sh > ./generated/x.c && gcc ./src/minus-omega.c ./generated/x.c ./src/main.c -lm -o program && ./program
