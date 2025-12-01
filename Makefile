
CompileGenerator: $(shell find . -name '*.agda')
	agda --compile CGenerator.agda	

CompileGHC: $(shell find . -name '*.agda')
	agda --compile Implementations/FFT.agda

GenerateCCode: CompileGenerator
	./CGenerator && clang-format -i generated/*

CompileGCC: GenerateCCode $(wildcard ./src/*.c) $(wildcard ./generated/*.c)
	cc -DDOUBLE_REAL $(wildcard ./src/*.c) $(wildcard ./generated/*.c) -Wall -Wextra -Wconversion -lm -o program

clean:
	rm generated/*
	rm CGenerator
	rm program
	rm FFT
