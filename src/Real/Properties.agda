open import src.Real.Base using (RealBase)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Data.Nat.Base using (ℕ)


module src.Real.Properties (r : RealBase) where
  open RealBase r

  open import Algebra.Structures  { A = ℝ }_≡_
  open import Algebra.Definitions { A = ℝ }_≡_

  record RealProperties : Set₁ where
    field
      double-negative : ∀ (x : ℝ) → - (- x) ≡ x

      *-comm : Commutative _*_
      *-identityˡ : LeftIdentity  1ℝ _*_
      *-identityʳ : RightIdentity 1ℝ _*_
      *-zeroˡ     : LeftZero  0ℝ _*_
      *-zeroʳ     : RightZero 0ℝ _*_
      *ᵣ-assoc    : Associative _*_

--     /ᵣ-zeroₜ : ∀ (x : ℝ) → (0 ᵣ) / x  ≡ 0 ᵣ

      +-comm      : Commutative _+_
      +-identityˡ : LeftIdentity  0ℝ _+_
      +-identityʳ : RightIdentity 0ℝ _+_
      +-assoc     : Associative _+_

--     -ᵣ-identityʳ : ∀ (x : ℝ) → x - (0 ᵣ) ≡ x

--     neg-distrib-* : ∀ (x y : ℝ) → (- x) * y ≡ - (x * y)
--     *-cancels-/ : ∀ (x y : ℝ) → x * (y / x) ≡ y
