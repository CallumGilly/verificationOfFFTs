open import src.Real using (Real)
module src.FFT (r : Real) where

open import src.Matrix using (Ar; Shape; Position; ι; _⊗_; nest; map; foldr; unnest; ι-cons; nil; _==_; zip; iterate; transpose; zipWith)
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Fin.Base using (Fin; toℕ; splitAt) renaming (zero to fzero; suc to fsuc)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)
open import Function.Base using (_∘_)
open import src.VecMat using (arrToVec; vecToArr)

open import src.DFTMatrix r using (DFT)
open import src.Complex r using (ℂ; ℂfromℕ; _+_; _-_; _*_; ω; *-identityʳ; ω-N-0; _+_i; e^i_; e^0; e^i[-π])
open import src.ComplexMatrix r using (sigma)
open Real r using (ℝ; π; sin; cos; double-negative; _ᵣ; -ᵣ-identityʳ; *ᵣ-zeroᵣ; +ᵣ-identityˡ; *ᵣ-identityʳ;
    /ᵣ-zeroₜ; +ᵣ-identityʳ; neg-distrib-*; *ᵣ-comm; *ᵣ-assoc; *-cancels-/)
  renaming (_*_ to _*ᵣ_; _/_ to _/ᵣ_; _+_ to _+ᵣ_; -_ to neg_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

private
  variable
    N r₁ r₂ : ℕ

FFT₁ : Ar (ι N) ℂ → Ar (ι N) ℂ
FFT₁ arr = DFT arr

-- Taken from "Computational Frameworks for the Fast Fourier Transform"
-- ISBN 978-0-898712-85-8
-- 1.1.2
-- Fₙ : ∀ {N : ℕ} → Ar (ι N ⊗ ι N) ℂ
-- Fₙ {N} (ι p ⊗ ι q) = ω N ((toℕ p) *ₙ (toℕ q))--e^i (((-ᵣ (2 ᵣ)) *ᵣ π *ᵣ (toℕ p) ᵣ *ᵣ (toℕ q) ᵣ ) /ᵣ (n ᵣ))

--twiddles : Ar (ι r₁ ⊗ ι r₂) ℂ
--twiddles {r₁} {r₂} (ι k₁ ⊗ ι k₀) = ω (r₁ *ₙ r₂) (k₁ )
-- ω N k = e^i (((2 ᵣ) *ᵣ π *ᵣ (k ᵣ)) /ᵣ (N ᵣ))

transposeₛ : Shape → Shape
transposeₛ (ι x) = ι x
transposeₛ (s ⊗ p) = (transposeₛ p) ⊗ (transposeₛ s) 

_ₙ/ᵣ_ : ∀ {f : ℕ} → Fin f → ℕ → ℝ
_ₙ/ᵣ_ m n = ((toℕ m) ᵣ) /ᵣ (n ᵣ)

twiddle-sum : ∀ {s : Shape} → Position s → ℝ
twiddle-sum {ι n} (ι pos) = pos ₙ/ᵣ n
twiddle-sum {sₗ ⊗ sᵣ} (xₗ ⊗ xᵣ) = (twiddle-sum xₗ) +ᵣ (twiddle-sum xᵣ)

--Need to check the difference between neg and not neg, I belive thats the difference for DIT vs DIF
twiddles : ∀ {s : Shape} → Ar s ℂ
twiddles {s} p = e^i (((neg (2 ᵣ)) *ᵣ π *ᵣ (twiddle-sum p)) ) 

FFT : ∀ {s : Shape} → Ar s ℂ → Ar (transposeₛ s) ℂ
FFT {ι x     } arr = DFT arr -- Use the DFT when no splitting is defined 
FFT {sₗ  ⊗ sᵣ} arr = let innerDFTapplied       = unnest (map FFT (nest arr)) in
                     let twiddleFactorsApplied = zipWith _*_ innerDFTapplied twiddles in
                     unnest (map FFT (nest (transpose twiddleFactorsApplied)))

