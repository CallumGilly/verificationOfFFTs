{-# OPTIONS --guardedness #-}

open import Implementations.Complex 
open import Real using (Real)
open import Implementations.Real using (realImplementation; showℝ)
--open import Complex using (Cplx)
open import ComplexNew
open import Implementations.Complex realImplementation using (complexImplementation; _+_i; fromℝ)

open Real.Real realImplementation using (ℝ; _ᵣ; -_)
open Cplx complexImplementation using (ℂ)

open Cplx ?

module CodeGeneration.RunTranslate where

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



RandAr : ∀ {ℓ : L} → (s : S ℓ) → IO (Ar s ℂ)

main : Main
main = run do
  ?
