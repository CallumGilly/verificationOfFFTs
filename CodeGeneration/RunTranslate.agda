{-# OPTIONS --guardedness #-}

open import Real using (Real)
open import Implementations.Real using (realImplementation; showℝ)
--open import Complex using (Cplx)
open import ComplexNew using (Cplx)
open import Implementations.ComplexNew --using (complexImplementation) --(complexImplementation; _+_i; fromℝ)
--open Base using (complexImplemenation)

open Real.Real realImplementation using (ℝ; _ᵣ) renaming (-_ to -ᵣ_)

--open import Effect.Monad.Random
open import System.Random hiding ()
open InBounds
open Float using () renaming (randomIO to randFloat; randomRIO to randRFloat)
open Vec using () renaming (randomIO to randVec)

open Cplx (complexImplementation realImplementation)

--open Cplx ?

module CodeGeneration.RunTranslate where

open import Data.Nat
open import Data.Fin using (toℕ)
open import Data.Nat.Show renaming (show to showℕ)

open import Matrix.NatMon
open import Matrix.Leveled.Base ℕ-Mon
open import Matrix.Leveled.Reshape ℕ-Mon

open import CodeGeneration.DSL
--open import CodeGeneration.Translate-C
--open import CodeGeneration.Translate-Agda 


open import IO 
open import IO.Finite
open import Data.String hiding (length; toVec; fromVec; tail; head)
open import Function

showℂ : ℂ → String
showℂ (real-component + imaginary-component i) = showℝ real-component ++ ", " ++ showℝ imaginary-component

open import Matrix.Leveled.Show ℂ showℂ

randℂ : IO ℂ
randℂ = (λ re im → (re .value) + (im .value) i) <$> (randRFloat (-ᵣ (400 ᵣ)) (400 ᵣ) _) <*> (randRFloat (-ᵣ (400 ᵣ)) (400 ᵣ) _)


open import Data.Vec.Functional hiding (length; _++_; _>>=_)

private variable
  X : Set
  ℓ : L
  s : S ℓ
  n m : ℕ

module _ where

  ArFromVector′ : ∀ {n : ℕ} → Vector X (suc n) → Ar (ν n) X
  ArFromVector′ xs (ν j) = xs j

  length-flattenᵣ : ∀ {s : S ℓ} → Reshape s (ν (length s))
  length-flattenᵣ {.(ss _)} {s ⊗ s₁} = flat ∙ (up length-flattenᵣ ⊕ up length-flattenᵣ)
  length-flattenᵣ {.zz} {ν x} = eq
  length-flattenᵣ {.(ss _)} {ι s} = down length-flattenᵣ

  ArFromVector : Vector X (suc $ length s) → Ar s X
  ArFromVector = reshape (rev length-flattenᵣ) ∘ ArFromVector′ 

  ArToVector′ : ∀ {n : ℕ} → Ar (ν n) X → Vector X (suc n)
  ArToVector′ xs j = xs (ν j)

  ArToVector : Ar s X → Vector X (suc $ length s)
  ArToVector = ArToVector′ ∘ reshape length-flattenᵣ

  randAr : ∀ {ℓ : L} → (s : S ℓ) → IO (Ar s ℂ)
  randAr s = ArFromVector ∘ fromVec <$> randVec randℂ (suc $ length s)

  showVectorLine : (X → String) → Vector X (suc n) → String
  showVectorLine show xs = foldl (λ existing new → existing ++ ", " ++ show new) (show $ head xs) (tail xs)

  open import Data.Product
  showVectorGrid : (X → String) → String → Vector (Vector X (suc n)) (suc m) → String
  showVectorGrid show header xs = (foldl (λ existing new → (suc (existing .proj₁)) , ((existing .proj₂) ++ "\n" ++ showℕ (existing .proj₁) ++ ", " ++ showVectorLine show new)) (0 , header) (transpose xs)) .proj₂


index : ∀ (n : ℕ) → Ar (ν n) ℕ
index _ (ν j) = toℕ j

level : L
level = ss (ss zz)

shape : S level
shape = ι (ι (ν 3) ⊗ ι (ν 4)) ⊗ ι (ι (ν 3) ⊗ ι (ν (2)))

header : String
header = "Index, Input-Real, Input-Imag, DFT-Real, DFT-Imag, FFT-Real, FFT-Imag, DFT-FFT-Diff-Real, DFT-FFT-Diff-Imag"

zeroAr : Ar s ℂ
zeroAr x = (0 ᵣ) + (0 ᵣ) i

open import CodeGeneration.Translate-Agda (complexImplementation realImplementation)
open import Matrix.Leveled.NatMon-Change-Major
open import FFT.Leveled.Specification
open import FFT.Leveled.dft (complexImplementation realImplementation)
open import FFT.Leveled.Properties (complexImplementation realImplementation) ℕ-Mon ℕ-CM ℕ-dft
open FFT-Specification ℕ-dft

fft-from-DSL : ∀ {s : S (ss (ss zz))} → Ar (ι s) ℂ → Ar (ι s) ℂ
fft-from-DSL = translate-Inp (fftn` _)

main : Main
main = run do

  input ← randAr shape
  let inputAsVec = ArToVector input

  --let dftAsVec = ArToVector $ dft (reshape length-flattenᵣ input) 
  let dftAsVec = ArToVector $ fftn input 
  --let dftAsVec = ArToVector $ reshape (down eq) (fft-from-DSL (reshape (up eq) input))
  let fftAsVec = ArToVector $ reshape (down eq) (fft-from-DSL (reshape (up eq) input))
  let diffAsVec = ArToVector $ zeroAr {_} {shape}

  let vecsToShow = inputAsVec ∷ dftAsVec ∷ fftAsVec ∷ diffAsVec ∷ []
  putStrLn (showVectorGrid showℂ header vecsToShow)


















