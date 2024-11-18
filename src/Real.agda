module src.Real where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat.Base using (ℕ)

record Real : Set₁ where

  infixl 7 _*ᵣ_
  infix   9 _ᵣ
  infixr 8 -ᵣ_

  field
    ℝ : Set

    _ᵣ :    ℕ → ℝ
    π    : ℝ

    _+ᵣ_ : ℝ → ℝ → ℝ
    _-ᵣ_ : ℝ → ℝ → ℝ
    _*ᵣ_ : ℝ → ℝ → ℝ
    _/ᵣ_ : ℝ → ℝ → ℝ
    -ᵣ_ : ℝ → ℝ

    cos : ℝ → ℝ
    sin : ℝ → ℝ
    
--     +ᵣ-commᵣ  : ∀ (x y   : ℝ) → (x +ᵣ y) ≡ (y +ᵣ x)
--     *ᵣ-commᵣ  : ∀ (x y   : ℝ) → (x *ᵣ y) ≡ (y *ᵣ x)
-- 
--     +ᵣ-assocᵣ : ∀ (x y z : ℝ) → (x +ᵣ y) +ᵣ z ≡ x +ᵣ (y +ᵣ z)
--     *ᵣ-assocᵣ : ∀ (x y z : ℝ) → (x *ᵣ y) *ᵣ z ≡ x *ᵣ (y *ᵣ z)
-- 
    +ᵣ-identityˡ : ∀ (x : ℝ) → (0 ᵣ) +ᵣ x ≡ x
--  *ᵣ-identityˡ : ∀ (x : ℝ) → (1 ᵣ) *ᵣ x ≡ x
-- 
--     +ᵣ-identityʳ : ∀ (x : ℝ) → x +ᵣ (fromℕ 0) ≡ x
    -ᵣ-identityʳ : ∀ (x : ℝ) → x -ᵣ (0 ᵣ) ≡ x
    *ᵣ-identityʳ : ∀ (x : ℝ) → x *ᵣ (1 ᵣ) ≡ x
--     /ᵣ-identityʳ : ∀ (x : ℝ) → x /ᵣ (fromℕ 1) ≡ x
    
