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
  let s = (ι ((ι (ν 2)) ⊗ (ι (ν 3)))) --((ι (ι (ν 4) ⊗ ι (ν 5))) ⊗ ι (ι (ν 3) ⊗ ι (ν 6)))
  let DEF = sizeDef s "fftn"
  writeFile "./generated/FFT.c" $ header ++ DEF ++ (fftn-test′     s)
  writeFile "./generated/FFT.h" $ header ++ DEF ++ (fftn-test-sig′ s)
  
