open import src.Real using (Real)
module src.Proof (r : Real) where

open import Data.Nat.Base using (ℕ; _*_)
open import Data.Fin.Base using (Fin; quotRem)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)

open import src.Matrix using (Ar; Shape; _⊗_; ι; flattern; _==_; transpose)
open import src.Complex r using (ℂ)
open import src.FFT r using (FFT)
open import src.DFTMatrix r using (DFT)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

theorm₁ : ∀ {n : ℕ} (arr : Ar (ι n) ℂ) → DFT arr == FFT arr
theorm₁ arr (ι x) = refl

theorm₂ : ∀ {n m : ℕ} (arr : Ar (ι n ⊗ ι m) ℂ) → DFT (flattern arr) == flattern (transpose (FFT arr))
theorm₂ arr (ι x) = ?

theorm : ∀ {s : Shape} (arr : Ar s ℂ) → DFT (flattern arr) == flattern (transpose (FFT arr))
-- theorm′ : ∀ {n : ℕ} (arr : Ar (ι n) ℂ) (reshape : Reshape (ι n)) → DFT arr == (FFT (arr ⟨ reshape ⟩ )) ⟨ rev reshape ⟩
