open import src.Real using (Real)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Data.Nat.Base using (ℕ)
open import Function using (_∘_)

open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)

module src.Complex (r : Real) where
  open Real r using (ℝ; _+ᵣ_; -ᵣ_; π; _-ᵣ_; _/ᵣ_; _*ᵣ_; sin; cos; fromℕ; double-negative; _ᵣ; -ᵣ-identityʳ; *ᵣ-zeroᵣ; +ᵣ-identityˡ; *ᵣ-identityʳ)

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

  -- Eulers Formula
  e^i_ : ℝ → ℂ
  e^i_ x = (cos x) + (sin x) i
  
