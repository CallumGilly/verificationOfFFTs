{-# OPTIONS --guardedness #-}

module Implementations.FFT where

open import Real using (Real)
open import Implementations.Real using (realImplementation; showℝ)
open import Complex using (Cplx)
open import Implementations.Complex realImplementation using (complexImplementation; _+_i; fromℝ)

open Real.Real realImplementation using (ℝ; _ᵣ; -_)
open Cplx complexImplementation using (ℂ)

open import Matrix
open import Matrix.Reshape
open import Matrix.Show using (showShape) renaming (show to showTensor)
open import Matrix.NonZero using (nonZeroDec)

open import FFT complexImplementation using (FFT; DFT)

open import IO using (IO; run; Main; _>>_; _>>=_)
open import IO.Finite using (putStrLn)
open import Relation.Nullary
open import Data.Unit.Polymorphic.Base using (⊤)
open import Agda.Builtin.String

open import Data.Nat.Show renaming (show to showNat)

open import Level

open import Function.Base using (_$_; _∘_)

open import CLang
open Interp realImplementation complexImplementation using (interp-inp)

private
  variable
   a : Level

private
  infixl 4 _++_
  _++_ : String → String → String
  _++_ = primStringAppend

--------------------
--- Show Complex ---
--------------------

showℂ : ℂ → String
showℂ (real + imaginary i) = (showℝ real) ++ " + " ++ (showℝ imaginary) ++ " i"

showDemoℂ : IO {a} ⊤
showDemoℂ = putStrLn $ showℂ ((4 ᵣ) + (2 ᵣ) i)

demo-mat₁ : Ar (ι 4 ⊗ (ι 4 ⊗ ι 3)) ℂ
demo-mat₁ = reshape ( eq ⊕ split ∙ split) demo-mat₁-vec
  where
    demo-mat₁-vec : Ar (ι 48) ℂ
    demo-mat₁-vec =
      ι-cons (fromℝ $   87  ᵣ) $
      ι-cons (fromℝ $   13  ᵣ) $
      ι-cons (fromℝ $   72  ᵣ) $
      ι-cons (fromℝ $ - 44  ᵣ) $
      ι-cons (fromℝ $   99  ᵣ) $
      ι-cons (fromℝ $   8   ᵣ)  $
      ι-cons (fromℝ $ - 63  ᵣ) $
      ι-cons (fromℝ $   25  ᵣ) $
      ι-cons (fromℝ $   90  ᵣ) $
      ι-cons (fromℝ $ - 31  ᵣ) $
      ι-cons (fromℝ $   56  ᵣ) $
      ι-cons (fromℝ $   19  ᵣ) $
      ι-cons (fromℝ $ - 100 ᵣ) $
      ι-cons (fromℝ $   37  ᵣ) $
      ι-cons (fromℝ $   4   ᵣ) $
      ι-cons (fromℝ $   15  ᵣ) $
      ι-cons (fromℝ $   50  ᵣ) $
      ι-cons (fromℝ $   14  ᵣ) $
      ι-cons (fromℝ $   80  ᵣ) $
      ι-cons (fromℝ $   15  ᵣ) $
      ι-cons (fromℝ $   50  ᵣ) $
      ι-cons (fromℝ $   14  ᵣ) $
      ι-cons (fromℝ $   80  ᵣ) $
      ι-cons (fromℝ $   61  ᵣ) $
      ι-cons (fromℝ $   87  ᵣ) $
      ι-cons (fromℝ $   13  ᵣ) $
      ι-cons (fromℝ $   72  ᵣ) $
      ι-cons (fromℝ $ - 44  ᵣ) $
      ι-cons (fromℝ $   99  ᵣ) $
      ι-cons (fromℝ $   8   ᵣ)  $
      ι-cons (fromℝ $ - 63  ᵣ) $
      ι-cons (fromℝ $   25  ᵣ) $
      ι-cons (fromℝ $   90  ᵣ) $
      ι-cons (fromℝ $ - 31  ᵣ) $
      ι-cons (fromℝ $   56  ᵣ) $
      ι-cons (fromℝ $   19  ᵣ) $
      ι-cons (fromℝ $ - 100 ᵣ) $
      ι-cons (fromℝ $   37  ᵣ) $
      ι-cons (fromℝ $   4   ᵣ) $
      ι-cons (fromℝ $   15  ᵣ) $
      ι-cons (fromℝ $   50  ᵣ) $
      ι-cons (fromℝ $   14  ᵣ) $
      ι-cons (fromℝ $   80  ᵣ) $
      ι-cons (fromℝ $   15  ᵣ) $
      ι-cons (fromℝ $   50  ᵣ) $
      ι-cons (fromℝ $   14  ᵣ) $
      ι-cons (fromℝ $   80  ᵣ) $
      ι-cons (fromℝ $   61  ᵣ) nil
      

demo-mat₂ : Ar (ι 12 ⊗ (ι 4 ⊗ ι 3)) ℂ
demo-mat₂ = reshape ((eq ⊕ split) ∙ split ) demo-mat₂-vec
  where
    demo-mat₂-vec : Ar (ι 144) ℂ
    demo-mat₂-vec =
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ)  $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 3 ᵣ) $
      ι-cons (fromℝ $ 1 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) $
      ι-cons (fromℝ $ 10 ᵣ) $
      ι-cons (fromℝ $ 5 ᵣ) nil

demo-mat₃ : Ar (ι 2 ⊗ (ι 2)) ℂ
demo-mat₃ = reshape ( eq ∙ split) demo-mat₁-vec
  where
    demo-mat₁-vec : Ar (ι 4) ℂ
    demo-mat₁-vec =
      ι-cons (fromℝ $ - 31  ᵣ) $
      ι-cons (fromℝ $   61  ᵣ) $ 
      ι-cons (fromℝ $ - 31  ᵣ) $
      ι-cons (fromℝ $   61  ᵣ) nil

show-arr             : Ar s ℂ → IO {a} ⊤
show-flat-arr        : Ar s ℂ → IO {a} ⊤
show-flat-FFT-result : Ar s ℂ → IO {a} ⊤
show-flat-DFT-result : Ar s ℂ → IO {a} ⊤

show-arr             xs = putStrLn $ "Tensor:     " ++ (showTensor showℂ $ xs)
show-flat-arr        xs = putStrLn $ "Flat Tensor:" ++ (showTensor showℂ $ reshape flatten-reindex xs)
show-flat-FFT-result {s} xs with nonZeroDec s
... | no ¬a = putStrLn "ERROR"
... | yes a = putStrLn $ "FFT Result: " ++ (showTensor showℂ $ reshape (rev ♯) ((interp-inp (`ffti a)) xs))
show-flat-DFT-result xs = putStrLn $ "DFT Result: " ++ (showTensor showℂ $ (DFT (reshape flatten-reindex xs)))

show-full-stack : Ar s ℂ → IO {a} ⊤
show-full-stack xs = do
  show-arr             xs
  show-flat-arr        xs
  show-flat-FFT-result xs
  show-flat-DFT-result xs

main : Main
main = run $ show-full-stack demo-mat₃

--fft≅dft : 
--    ∀ (arr : Ar s ℂ) 
--  → FFT arr 
--    ≅ 
--    ( (reshape ♯) 
--    ∘ DFT
--    ∘ (reshape flatten-reindex)) arr
