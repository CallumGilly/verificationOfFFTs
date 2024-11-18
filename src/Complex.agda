open import src.Real using (Real)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

open import Data.Nat.Base using (ℕ)
open import Function using (_∘_)

open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)

module src.Complex (r : Real) where
  open Real r using (ℝ; _+ᵣ_; -ᵣ_; π; _-ᵣ_; _/ᵣ_; _*ᵣ_; sin; cos; fromℕ; double-negative; _ᵣ; -ᵣ-identityʳ; *ᵣ-zeroᵣ; +ᵣ-identityˡ; *ᵣ-identityʳ; /ᵣ-zeroₜ)

  infixl 7 _*_
  infixl 6 _+_ _-_

  record ℂ : Set where
    constructor _+_i
    field
      real      : ℝ
      imaginary : ℝ
  
  RealPart      : ℂ → ℝ
  RealPart      = ℂ.real
  ImaginaryPart : ℂ → ℝ
  ImaginaryPart = ℂ.imaginary

  fromℝ : ℝ → ℂ
  fromℝ x = x + (0 ᵣ) i

  ℂfromℕ : ℕ → ℂ
  ℂfromℕ = fromℝ ∘ _ᵣ

  _+_ : ℂ → ℂ → ℂ
  (xRe + xIm i) + (yRe + yIm i) = (xRe +ᵣ yRe) + (xIm +ᵣ yIm) i
  --x + y = (RealPart x +ᵣ RealPart y) + (ImaginaryPart x +ᵣ ImaginaryPart y) i

  _-_ : ℂ → ℂ → ℂ
  (xRe + xIm i) - (yRe + yIm i) = (xRe -ᵣ yRe) + (xIm -ᵣ yIm) i

  _*_ : ℂ → ℂ → ℂ
  (xRe + xIm i) * (yRe + yIm i) = ((xRe *ᵣ yRe) -ᵣ (xIm *ᵣ yIm)) + ((xRe *ᵣ yIm) +ᵣ (xIm *ᵣ yRe)) i

  *-identityʳ : ∀ {n : ℂ} → n * (ℂfromℕ 1) ≡ n
  *-identityʳ {real + imaginary i} =
    begin
      (real + imaginary i) * ℂfromℕ 1
    ≡⟨⟩
      (real + imaginary i) * ((1 ᵣ) + (0 ᵣ) i)
    ≡⟨⟩
      ((real *ᵣ 1 ᵣ) -ᵣ (imaginary *ᵣ 0 ᵣ)) + ((real *ᵣ 0 ᵣ) +ᵣ (imaginary *ᵣ 1 ᵣ)) i
    ≡⟨ cong (_+ ((real *ᵣ 0 ᵣ) +ᵣ (imaginary *ᵣ 1 ᵣ)) i) (cong (λ x → (real *ᵣ 1 ᵣ) -ᵣ x) *ᵣ-zeroᵣ) ⟩
      ((real *ᵣ 1 ᵣ) -ᵣ (0 ᵣ)) + ((real *ᵣ 0 ᵣ) +ᵣ (imaginary *ᵣ 1 ᵣ)) i
    ≡⟨ cong (_+ ((real *ᵣ 0 ᵣ) +ᵣ (imaginary *ᵣ 1 ᵣ)) i) (-ᵣ-identityʳ (real *ᵣ 1 ᵣ)) ⟩
      (real *ᵣ 1 ᵣ) + ((real *ᵣ 0 ᵣ) +ᵣ (imaginary *ᵣ 1 ᵣ)) i
    ≡⟨ cong ((real *ᵣ 1 ᵣ) +_i) (cong (_+ᵣ (imaginary *ᵣ 1 ᵣ)) *ᵣ-zeroᵣ) ⟩
      (real *ᵣ 1 ᵣ) + ((0 ᵣ) +ᵣ (imaginary *ᵣ 1 ᵣ)) i
    ≡⟨ cong ((real *ᵣ 1 ᵣ) +_i) (+ᵣ-identityˡ (imaginary *ᵣ 1 ᵣ)) ⟩
      (real *ᵣ 1 ᵣ) + ((imaginary *ᵣ 1 ᵣ)) i
    ≡⟨ cong ((real *ᵣ 1 ᵣ) +_i) (*ᵣ-identityʳ imaginary) ⟩
      (real *ᵣ 1 ᵣ) + imaginary i
    ≡⟨ cong (_+ imaginary i) (*ᵣ-identityʳ real) ⟩
      real + imaginary i
    ∎

  -- Eulers Formula
  e^i_ : ℝ → ℂ
  e^i_ x = (cos x) + (sin x) i

  postulate
    e^0 : e^i (0 ᵣ) ≡ ℂfromℕ 1 

  ℂ-conjugate : ℂ → ℂ
  ℂ-conjugate (real + imaginary i) = real + (-ᵣ imaginary) i

  ω : ∀ (N : ℕ) (k : ℕ) → ℂ
  ω N k = e^i (((-ᵣ (2 ᵣ)) *ᵣ π *ᵣ (k ᵣ)) /ᵣ (N ᵣ))

  ω-N-0 : ∀ {N : ℕ} → ω N 0 ≡ ℂfromℕ 1
  ω-N-0 {N} =
    begin
      ω N 0
    ≡⟨⟩
      e^i (((-ᵣ 2 ᵣ *ᵣ π) *ᵣ (0 ᵣ)) /ᵣ (N ᵣ))
    ≡⟨ cong (e^i_) (cong (_/ᵣ (N ᵣ)) *ᵣ-zeroᵣ) ⟩
      e^i ((0 ᵣ) /ᵣ (N ᵣ))
    ≡⟨ cong (e^i_) /ᵣ-zeroₜ ⟩
      e^i (0 ᵣ)
    ≡⟨ e^0 ⟩
      ℂfromℕ 1
    ∎


