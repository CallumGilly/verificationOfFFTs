module src.reals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

record Real : Set₁ where
  field
    ℝ : Set
   -- Every definiton of the reals needs some zero and one value, to allow for identity functions to be defined
    zero : ℝ
    one  : ℝ 
    _+ᵣ_ : ℝ → ℝ → ℝ
    _-ᵣ_ : ℝ → ℝ → ℝ
    _*ᵣ_ : ℝ → ℝ → ℝ
    _/ᵣ_ : ℝ → ℝ → ℝ
    
    +ᵣ-commᵣ  : ∀ (x y   : ℝ) → (x +ᵣ y) ≡ (y +ᵣ x)
    *ᵣ-commᵣ  : ∀ (x y   : ℝ) → (x *ᵣ y) ≡ (y *ᵣ x)

    +ᵣ-assocᵣ : ∀ (x y z : ℝ) → (x +ᵣ y) +ᵣ z ≡ x +ᵣ (y +ᵣ z)
    *ᵣ-assocᵣ : ∀ (x y z : ℝ) → (x *ᵣ y) *ᵣ z ≡ x *ᵣ (y *ᵣ z)

    +ᵣ-identityˡ : ∀ (x : ℝ) → zero +ᵣ x ≡ x
    *ᵣ-identityˡ : ∀ (x : ℝ) → one  *ᵣ x ≡ x

    +ᵣ-identityʳ : ∀ (x : ℝ) → x +ᵣ zero ≡ x
    -ᵣ-identityʳ : ∀ (x : ℝ) → x -ᵣ zero ≡ x
    *ᵣ-identityʳ : ∀ (x : ℝ) → x *ᵣ one  ≡ x
    /ᵣ-identityʳ : ∀ (x : ℝ) → x /ᵣ one  ≡ x
    
