
CompileGenerator: $(shell find . -name '*.agda')
	agda --compile CGenerator.agda	

CompileGHC: $(shell find . -name '*.agda')
	agda --compile Implementations/FFT.agda

GenerateCCode: CompileGenerator
	./CGenerator && clang-format -i generated/*

CompileGCCWithoutGeneration: $(wildcard ./src/*.c)
	cc -DDOUBLE_REAL $(wildcard ./src/*.c) ./generated/*.c -Wall -Wextra -Wconversion -pedantic -lm -o program

# As we are creating new files, we have to use the shell's expansion of globs 
# to expand the contents of ./generated, otherwise make will try to check its 
# cache and will miss the newly created files after `make clean`
CompileGCC: GenerateCCode CompileGCCWithoutGeneration $(wildcard ./src/*.c)

CompileClang: GenerateCCode $(wildcard ./src/*.c)
	clang -DDOUBLE_REAL $(wildcard ./src/*.c) ./generated/*.c -Warray-bounds-pointer-arithmetic -Wall -Wextra -Wconversion -pedantic -lm -o program

clean:
	rm -f generated/*
	rm -f CGenerator
	rm -f program
	rm -f FFT
