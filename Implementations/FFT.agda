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
open import Matrix.Show using (showShape; showCSV) renaming (show to showTensor)
open import Matrix.NonZero using (nonZeroDec)

open import FFT complexImplementation using (FFT; DFT)
open import FFT-Vec complexImplementation

open import IO using (IO; run; Main; _>>_; _>>=_)
open import IO.Finite using (putStrLn)
open import Relation.Nullary
open import Data.Unit.Polymorphic.Base using (⊤)
open import Agda.Builtin.String

open import Data.Nat.Show renaming (show to showNat)
open import Data.Fin renaming (suc to +; zero to z)

open import Level

open import Function.Base using (_$_; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong)

--open import CLang
--open Interp realImplementation complexImplementation using (interp-inp)

private
  variable
   a : Level
   s : Shape

private
  infixl 4 _++_
  _++_ : String → String → String
  _++_ = primStringAppend

--------------------
--- Show Complex ---
--------------------

showℂ : ℂ → String
showℂ (real + imaginary i) = (showℝ real) ++ " + " ++ (showℝ imaginary) ++ " i"

showℂSV : ℂ → String
showℂSV (real + imaginary i) = (showℝ real) ++ ", " ++ (showℝ imaginary)

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

demo-mat₄ : Ar ((ι 2 ⊗ ι 2) ⊗ ι 2) ℂ
demo-mat₄ = reshape ( split ⊕ eq ∙ split) demo-mat₁-vec
  where
    demo-mat₁-vec : Ar (ι 8) ℂ
    demo-mat₁-vec =
      ι-cons (fromℝ $ - 31  ᵣ) $
      ι-cons (fromℝ $   23  ᵣ) $ 
      ι-cons (fromℝ $ - 54  ᵣ) $
      ι-cons (fromℝ $ - 43  ᵣ) $
      ι-cons (fromℝ $ - 12  ᵣ) $
      ι-cons (fromℝ $   61  ᵣ) $ 
      ι-cons (fromℝ $ - 56  ᵣ) $
      ι-cons (fromℝ $   91  ᵣ) nil

open import Implementations.VeryLargeShapeAuto
--postulate
--  SIMD-demo-vec : Ar (ι 240) ℂ

SIMD-Shape : Shape
--SIMD-Shape = (((ι V ⊗ ι 3) ⊗ (ι V ⊗ ι 5)))
SIMD-Shape = (((ι V ) ⊗ ((ι 3 ⊗ ι V) ⊗ ι 5)))
SIMD-demo : Ar SIMD-Shape ℂ
--SIMD-demo = reshape (split ⊕ split ∙ split) SIMD-demo-vec
SIMD-demo = reshape ( eq ⊕ ((split ⊕ eq) ∙ split) ∙ split) SIMD-demo-vec

show-arr                  : Ar s ℂ → IO {a} ⊤
show-flat-arr             : Ar s ℂ → IO {a} ⊤
--show-flat-Inp-FFT-result  : Ar s ℂ → IO {a} ⊤
show-flat-Orig-FFT-result : Ar s ℂ → IO {a} ⊤
show-flat-DFT-result      : Ar s ℂ → IO {a} ⊤


show-arr             xs =          putStrLn $ "Tensor:          " ++ (showTensor showℂ $ xs)
show-flat-arr        xs =          putStrLn $ "Flat Tensor:     " ++ (showTensor showℂ $ reshape flatten-reindex xs)
--show-flat-Inp-FFT-result {s} xs with nonZeroDec s
--... | no ¬a = putStrLn "ERROR"
--... | yes a = putStrLn $ "Inp FFT Result: " ++ (showTensor showℂ $ reshape (rev ♯) ((interp-inp (`ffti a)) xs))
--show-flat-Orig-FFT-result {s} xs = putStrLn $ "Orig FFT Result: " ++ (showTensor showℂ $ reshape (rev ♯) (FFT xs))
show-flat-Orig-FFT-result {s} xs = putStrLn $ "Orig FFT Result: " ++ (showTensor showℂ $ reshape (rev ♯) (ufft′ xs))
show-flat-DFT-result xs          = putStrLn $ "DFT Result:      " ++ (showTensor showℂ $ (DFT (reshape flatten-reindex xs)))

show-full-stack : Ar s ℂ → IO {a} ⊤
show-full-stack xs = do
  show-arr             xs
  show-flat-arr        xs
  --show-flat-Inp-FFT-result xs
  show-flat-Orig-FFT-result xs
  show-flat-DFT-result xs

CSVStack : Ar s ℂ → Ar (ι 3 ⊗ ι (length s)) ℂ
CSVStack xs     (ι z ⊗ x₁)         = (reshape ♭ xs) x₁
CSVStack {s} xs (ι (+ z) ⊗ x₁)     = reshape (reindex (sym (|s|≡|sᵗ| {s}))) (DFT (reshape flatten-reindex xs)) x₁
CSVStack xs     (ι (+ (+ z)) ⊗ x₁) = reshape ♭ (ufft xs) x₁


OFFTStack : Ar (ι 3 ⊗ ι (length SIMD-Shape)) ℂ
OFFTStack (ι z ⊗ x₁)         = (reshape ♭ SIMD-demo) x₁
OFFTStack (ι (+ z) ⊗ x₁)     = (DFT (reshape flatten-reindex SIMD-demo)) x₁
OFFTStack (ι (+ (+ z)) ⊗ x₁) = (reshape (♭) (nofft (ι) SIMD-demo)) x₁

--CSVStack xs (ι (+ (+ z)) ⊗ x₁) = reshape ♭ (offt ? ?) x₁

CSVStackHead : Ar (ι 3) String
CSVStackHead (ι z) =         " Input-Real" ++ ", " ++ "Input-Imag"
CSVStackHead (ι (+ z)) =     "DFT-Real"   ++ ", " ++ "DFT-Imag"
CSVStackHead (ι (+ (+ z))) = "FFT-Real"   ++ ", " ++ "FFT-Imag"

main : Main
main = run $ putStrLn $ showCSV showℂSV CSVStackHead (OFFTStack)

--main = run $ show-full-stack demo-mat₄

--fft≅dft : 
--    ∀ (arr : Ar s ℂ) 
--  → FFT arr 
--    ≅ 
--    ( (reshape ♯) 
--    ∘ DFT
--    ∘ (reshape flatten-reindex)) arr











