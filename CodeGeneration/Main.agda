{-# OPTIONS --guardedness #-}
module CodeGeneration.Main where

open import Matrix.NatMon
open import Matrix.Leveled ℕ-Mon
--open import Matrix.Leveled.Show ? ? 

open import CodeGeneration.DSL
open import CodeGeneration.Translate-C
--open import CodeGeneration.Translate-Agda


open import IO using (IO; run; Main; _>>_; _>>=_; putStrLn)
open import IO.Finite
open import Data.String
open import Function

header : String
header = "#include <complex.h>\n"
      ++ "#include <stddef.h>\n"
      ++ "#include <stdlib.h>\n"
      ++ "#include <stdio.h>\n"
      ++ "#include \"../src/minus-omega.h\"\n"

main : Main
main = run do
  ----- FFTN -----

  --let s = ((ι (ι (ν 1))) ⊗ (ι (ι (ν 1))))
  --let s = ( (ι (ι (ν 2))) ⊗ ( (ι (ι (ν 3))) ⊗ (ι (ι (ν 4))) ) )
  --let s =  (ι ((ι (ν 1))) ⊗  ((ι (ν 1)) ⊗ (ι (ν 1))))
  --let s =  ((ι (ι (ν 1) ⊗ ι (ν 1))) ⊗  (ι (ι (ν 1))))
  --let s = (ι ((ι (ν 1)) ⊗ ((ι (ν 1)) ⊗ (ι (ν 1)))))
  --let s = (ι ((ι (ν 1)) ⊗ ((ι (ν 2)) ⊗ (ι (ν 3)))))
  --let s = ((ι (ι (ν 1) ⊗ (ι (ν 1)))) ⊗ (ι (ι (ν 1))))
  let s = ((ι (ι (ν 2) ⊗ (ι (ν 3)))) ⊗ (ι (ι (ν 4))))

  {-
  let DEF = sizeDef-Complex s "fftn"
  writeFile "./generated/FFT.c" $ header ++ DEF ++ (fftn-test-Complex′     s)
  writeFile "./generated/FFT.h" $ header ++ DEF ++ (fftn-test-sig-Complex′ s)
  -}

  {-
  let DEF = sizeDef-Real s "fftn"
  writeFile "./generated/FFT.c" $ header ++ DEF ++ (fftn-test-Real′     s)
  writeFile "./generated/FFT.h" $ header ++ DEF ++ (fftn-test-sig-Real′ s)
  -}

  {-
  let DEF = sizeDefs (Scl R) s "fftn"
  writeFile "./generated/FFT.c" $ header ++ DEF ++ (fftn-test′     s)
  writeFile "./generated/FFT.h" $ header ++ DEF ++ (fftn-test-sig′ s)
  -}

  let DEF = sizeDef-Complex s "fftn"
  writeFile "./generated/FFT.c" $ header ++ DEF ++ (fftn-test-Complex′     s)
  writeFile "./generated/FFT.h" $ header ++ DEF ++ (fftn-test-sig-Complex′ s)


{-
sizeDef-Complex : S ℓ → String → String
sizeDef-Complex s name =     (printf "#ifndef %s_SIZE\n" name)
                  ++ (printf "#define %s_SIZE %u\n" name (clen s))
                  ++ (printf "typedef complex real (*%s_TYPE)%s;\n" name (ShapeCast s))
                  ++ ("#define ARR_OF_COMPLEX\n")
                  ++ "#endif\n"
module _ where

  fftn-test-sig-Complex′ : S (ss (ss zz)) → String
  fftn-test-sig-Complex′ s = inp-signature-Scl C (fftn` s) "fftn"

  fftn-test-sig′ : S (ss (ss zz)) → String
  fftn-test-sig′ s = inp-signature _ (Rfftn` s) "fftn"


  fftn-test-Complex′ : S (ss (ss zz)) → String
  fftn-test-Complex′ s =
    let fun = fftn` s in
    inp→f-Scl C fun "fftn"

  fftn-test′ : S (ss (ss zz)) → String
  fftn-test′ s =
    let fun = Rfftn` s in
    inp→f _ fun "fftn"
    -}

