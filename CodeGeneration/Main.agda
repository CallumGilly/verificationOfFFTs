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
  {-
  ----- Test Cases -----
  --let test₁-body = test₁
  --writeFile "./tests/test1.c" $ header ++ test₁-body

  --let test₂-body = test₂
  --writeFile "./tests/test2.c" $ header ++ test₂-body

  let test₃-body = test₃
  writeFile "./tests/test3.c" $ header ++ test₃-body

  let test₄-body = test₄
  writeFile "./tests/test4.c" $ header ++ test₄-body
  
  let test₅-body = test₅
  writeFile "./tests/test5.c" $ header ++ test₅-body
  -}
  
  
  ----- FFTN -----

  --let s = ((ι (ι (ν 1))) ⊗ (ι (ι (ν 1))))
  --let s = ( (ι (ι (ν 2))) ⊗ ( (ι (ι (ν 3))) ⊗ (ι (ι (ν 4))) ) )
  --let s =  (ι ((ι (ν 1))) ⊗  ((ι (ν 1)) ⊗ (ι (ν 1))))
  --let s =  ((ι (ι (ν 1) ⊗ ι (ν 1))) ⊗  (ι (ι (ν 1))))
  --let s = (ι ((ι (ν 1)) ⊗ ((ι (ν 1)) ⊗ (ι (ν 1)))))
  --let s = (ι ((ι (ν 1)) ⊗ ((ι (ν 2)) ⊗ (ι (ν 3)))))
  --let s = ((ι (ι (ν 1) ⊗ (ι (ν 1)))) ⊗ (ι (ι (ν 1))))
  let s = ((ι (ι (ν 2) ⊗ (ι (ν 3)))) ⊗ (ι (ι (ν 4))))

  --let DEF = sizeDef-Complex s "fftn"
  --writeFile "./generated/FFT.c" $ header ++ DEF ++ (fftn-test-Complex′     s)
  --writeFile "./generated/FFT.h" $ header ++ DEF ++ (fftn-test-sig-Complex′ s)
  
  let DEF = sizeDef-Real s "fftn"
  writeFile "./generated/FFT.c" $ header ++ DEF ++ (fftn-test-Real′     s)
  writeFile "./generated/FFT.h" $ header ++ DEF ++ (fftn-test-sig-Real′ s)
