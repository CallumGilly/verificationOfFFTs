{-# OPTIONS --guardedness #-}

open import Implementations.Complex 
open import Real using (Real)
open import Implementations.Real using (realImplementation; showℝ)
--open import Complex using (Cplx)
open import ComplexNew
open import Implementations.ComplexNew using (complexImplementation; _+_i; fromℝ)

open Real.Real realImplementation using (ℝ; _ᵣ; -_)

--open import Effect.Monad.Random
open import System.Random
--open Cplx complexImplementation using (ℂ)

--open Cplx ?

module CodeGeneration.RunTranslate where

open import Matrix.NatMon
open import Matrix.Leveled ℕ-Mon
open import Matrix.Leveled.Show ? ?

open import CodeGeneration.DSL
open import CodeGeneration.Translate-C
open import CodeGeneration.Translate-Agda 


open import IO using (IO; run; Main; _>>_; _>>=_; putStrLn)
open import IO.Finite
open import Data.String
open import Function

open import IO.Random

--ℂ : Set

--RandAr : ∀ {ℓ : L} → (s : S ℓ) → IO (Ar s ℂ)

main : Main
main = run do
  --a ← ransomIO
  ?

