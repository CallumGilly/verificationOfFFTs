module src.Real where

import Relation.Binary.PropositionalEquality as Eq
open import Agda.Builtin.String
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat.Base using (ℕ)

record Real : Set₁ where

  infixl 7 _*_
  infix   9 _ᵣ
  infixr 8 -_

  field
    ℝ : Set

    _ᵣ :    ℕ → ℝ
    π    : ℝ

    _+_ : ℝ → ℝ → ℝ
    _-_ : ℝ → ℝ → ℝ
    _*_ : ℝ → ℝ → ℝ
    _/_ : ℝ → ℝ → ℝ
    -_ : ℝ → ℝ

    cos : ℝ → ℝ
    sin : ℝ → ℝ

    double-negative : ∀ (x : ℝ) → - (- x) ≡ x

    *ᵣ-zeroᵣ : ∀ (x : ℝ) → x * (0 ᵣ)  ≡ 0 ᵣ
    /ᵣ-zeroₜ : ∀ (x : ℝ) → (0 ᵣ) / x  ≡ 0 ᵣ
    
    +ᵣ-comm : ∀ (x y   : ℝ) → (x + y) ≡ (y + x)
--     *ᵣ-commᵣ  : ∀ (x y   : ℝ) → (x *ᵣ y) ≡ (y *ᵣ x)
-- 
    +ᵣ-assoc     : ∀ (x y z : ℝ) → (x + y) + z ≡ x + (y + z)
--     *ᵣ-assocᵣ : ∀ (x y z : ℝ) → (x *ᵣ y) *ᵣ z ≡ x *ᵣ (y *ᵣ z)
-- 
    +ᵣ-identityˡ : ∀ (x : ℝ) → (0 ᵣ) + x ≡ x
--  *ᵣ-identityˡ : ∀ (x : ℝ) → (1 ᵣ) *ᵣ x ≡ x
-- 
    +ᵣ-identityʳ : ∀ (x : ℝ) → x + (0 ᵣ) ≡ x
    -ᵣ-identityʳ : ∀ (x : ℝ) → x - (0 ᵣ) ≡ x
    *ᵣ-identityʳ : ∀ (x : ℝ) → x * (1 ᵣ) ≡ x
--     /ᵣ-identityʳ : ∀ (x : ℝ) → x /ᵣ (fromℕ 1) ≡ x

    neg-distrib-* : ∀ (x y : ℝ) → (- x) * y ≡ - (x * y)
    
    *ᵣ-assoc : ∀ (x y z : ℝ) → (x * y) * z ≡ x * (y * z) 
    *ᵣ-comm  : ∀ (x y   : ℝ) →  x * y      ≡ y * x

    *-cancels-/ : ∀ (x y : ℝ) → x * (y / x) ≡ y

    show : ℝ → String


--isℕ  = ?

--data isℕ : ℝ → Set where
--  directFromℝ : ∀ {r : ℝ} {n : ℕ} → (n ᵣ) ≡ r


