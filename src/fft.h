  // preamble = "#include <complex.h>\n" 
  //          ++ "#include <stddef.h>\n"
  //          ++ "#include <stdlib.h>\n"
  //          ++ "#include \"../src/minus-omega.h\"\n"
  //          ++ "#include \"../src/dft.h\"\n"
  //          ++ "\n"

  // sizeDef : Shape → String → String
  // sizeDef s name =     (printf "#ifndef %s_SIZE\n" name)
  //                   ++ (printf "#define %s_SIZE %u\n" name (size s))
  //                   ++ (printf "typedef real (*%s_TYPE)%s;\n" name (shape-helper (ι 2 ⊗ s)))
  //                   ++ "#endif\n"


  // gen-fft : (s : Shape) → ⦃ _ : NonZeroₛ s ⦄ → ?SIMD s → String × String
  // gen-fft s pred with show′ (num (arr R)) (arr "inp" idh) (fft s pred) "fft"
  // ... | body , header = (preamble ++ (sizeDef s "fft") ++ header) , (preamble ++ (sizeDef s "fft") ++ body)
