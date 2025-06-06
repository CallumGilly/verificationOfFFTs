open import src.Real using (Real)
open import src.Complex using (Cplx)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning

open import Function using (_∘_)
open import Data.Nat using (ℕ)

module src.Complex.Implementation (real : Real) where
  open Real real using (ℝ; _ᵣ; cos; sin; π) renaming (-_ to -ᵣ_; _+_ to _+ᵣ_; _-_ to _-ᵣ_; _*_ to _*ᵣ_; _/_ to _/ᵣ_)

  module Base where
    private
      record ℂ₁ : Set where
        constructor _+_i
        field
          real-component      : ℝ
          imaginary-component : ℝ

      0ℂ  : ℂ₁
      0ℂ  = (    (0 ᵣ)  + (0 ᵣ) i)
      -1ℂ : ℂ₁
      -1ℂ = ((-ᵣ (1 ᵣ)) + (0 ᵣ) i)
      1ℂ  : ℂ₁
      1ℂ  = (    (1 ᵣ)  + (0 ᵣ) i)

      _+_ : ℂ₁ → ℂ₁ → ℂ₁
      _+_ (xRe + xIm i) (yRe + yIm i) = (xRe +ᵣ yRe) + (xIm +ᵣ yIm) i

      _-_ : ℂ₁ → ℂ₁ → ℂ₁
      _-_ (xRe + xIm i) (yRe + yIm i) = (xRe -ᵣ yRe) + (xIm -ᵣ yIm) i

      -_ : ℂ₁ → ℂ₁
      -_ (re + im i) = ((-ᵣ re) + (-ᵣ im) i)

      _*_ : ℂ₁ → ℂ₁ → ℂ₁
      _*_ (xRe + xIm i) (yRe + yIm i) = ((xRe *ᵣ yRe) -ᵣ (xIm *ᵣ yIm)) + ((xRe *ᵣ yIm) +ᵣ (xIm *ᵣ yRe)) i

      fromℝ : ℝ → ℂ₁
      fromℝ x = x + (0 ᵣ) i
      
      ℂfromℕ : ℕ → ℂ₁
      ℂfromℕ = fromℝ ∘ _ᵣ

      e^i_ : ℝ → ℂ₁
      e^i_ x = (cos x) + (sin x) i
      
      ℂ-conjugate : ℂ₁ → ℂ₁
      ℂ-conjugate (re + im i) = re + (-ᵣ im) i

      -ω : ∀ (N : ℕ) (k : ℕ) → ℂ₁
      -ω N k = e^i (((-ᵣ (2 ᵣ)) *ᵣ π *ᵣ (k ᵣ)) /ᵣ (N ᵣ))

    complexBaseImplementation : Cplx real
    complexBaseImplementation = record {
          ℂ = ℂ₁

        ; _+_ = _+_
        ; _-_ = _-_
        ; -_  = -_
        ; _*_ = _*_

        ; fromℝ = fromℝ
        ; ℂfromℕ = ℂfromℕ

        ; e^i_ = e^i_
        ; ℂ-conjugate = ℂ-conjugate

        ; -ω = -ω

        ; +-*-isCommutativeRing = ?
        ; ω-N-0                 = ?
        ; ω-N-mN                = ?
        ; ω-r₁x-r₁y             = ?
        ; ω-N-k₀+k₁             = ?
      }
  open Base public
  open Cplx complexBaseImplementation


