open import src.Real.Base using (RealBase)
open import src.Complex.Base using (CplxBase)
open import src.Complex.Properties using (CplxProperties)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning

open import Function using (_∘_)
open import Data.Nat using (ℕ)

module src.Complex.Implementation (realBase : RealBase) where
  open RealBase realBase using (ℝ; _ᵣ; cos; sin; π) renaming (-_ to -ᵣ_; _+_ to _+ᵣ_; _-_ to _-ᵣ_; _*_ to _*ᵣ_; _/_ to _/ᵣ_)

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

      +ω : ∀ (N : ℕ) (k : ℕ) → ℂ₁
      +ω N k = e^i (((2 ᵣ) *ᵣ π *ᵣ (k ᵣ)) /ᵣ (N ᵣ))

      -ω : ∀ (N : ℕ) (k : ℕ) → ℂ₁
      -ω N k = e^i (((-ᵣ (2 ᵣ)) *ᵣ π *ᵣ (k ᵣ)) /ᵣ (N ᵣ))

    complexBaseImplementation : CplxBase realBase
    complexBaseImplementation = record {
          ℂ = ℂ₁

        ; 0ℂ  = 0ℂ
        ; -1ℂ = -1ℂ
        ; 1ℂ  = 1ℂ

        ; _+_ = _+_
        ; _-_ = _-_
        ; -_  = -_
        ; _*_ = _*_

        ; fromℝ = fromℝ
        ; ℂfromℕ = ℂfromℕ

        ; e^i_ = e^i_
        ; ℂ-conjugate = ℂ-conjugate

        ; +ω = +ω
        ; -ω = -ω
      }
  open Base public
  open CplxBase complexBaseImplementation

  module Properties where
    open import Algebra.Structures {A = ℂ} _≡_
    open import Algebra.Definitions {A = ℂ} _≡_

    private
      *-cong           : Congruent₂ _*_
      *-cong           = ?
      *-assoc          : Associative _*_
      *-assoc          = ?
      *-identity       : Identity 1ℂ _*_
      *-identity       = ?
      distrib          : _*_ DistributesOver _+_
      distrib          = ?

      isGroup : IsGroup _+_ 0ℂ (-_)
      isGroup = record {
          isMonoid = ?
        ; inverse  = ?
        ; ⁻¹-cong  = ?
        }

      +-isAbelianGroup : IsAbelianGroup _+_ 0ℂ (-_)
      +-isAbelianGroup = record {
          isGroup = ?
        ; comm = ?
        }
      
      isRing : IsRing _+_ _*_ -_ 0ℂ 1ℂ
      isRing = record {
          +-isAbelianGroup = +-isAbelianGroup
        ; *-cong           = *-cong
        ; *-assoc          = *-assoc
        ; *-identity       = *-identity
        ; distrib          = distrib
        }
      
      +-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0ℂ 1ℂ
      +-*-isCommutativeRing = record {
          isRing = isRing
        ; *-comm = ?
        }

    complexPropertiesImplementation : CplxProperties realBase complexBaseImplementation
    complexPropertiesImplementation = record {
        +-identityʳ           = ?
      ; *-comm                = ?
      ; *-identityʳ           = ?
      ; *-zeroˡ               = ?
      ; *-cong                = *-cong
      ; *-assoc               = *-assoc
      ; *-identity            = *-identity
      ; distrib               = distrib
      ; +-isAbelianGroup      = +-isAbelianGroup
      ; isRing                = isRing
      ; +-*-isCommutativeRing = +-*-isCommutativeRing
      ; ω-N-0                 = ?
      ; ω-N-mN                = ?
      ; ω-r₁x-r₁y             = ?
      }
  open Properties public

    





