open import src.reals using (Real)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Data.Nat.Base using (ℕ)
open import Function using (_∘_)

open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)

module src.complex (r : Real) where
  open Real r using (ℝ; _+ᵣ_; _-ᵣ_; _*ᵣ_; sin; cos; fromℕ)

  infixl 7 _*_

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
  fromℝ x = x + (fromℕ 0) i

  ℂfromℕ : ℕ → ℂ
  ℂfromℕ = fromℝ ∘ fromℕ

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
  
