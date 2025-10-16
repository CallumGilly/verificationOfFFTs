open import Real using (Real)

open import Data.Nat.Base using (ℕ; NonZero; suc) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties using (m*n≢0)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning

module Complex where

  import Algebra.Structures as AlgebraStructures
  import Algebra.Definitions as AlgebraDefinitions

  record Cplx : Set₁ where
    infix  8 -_
    infixl 7 _*_
    infixl 6 _+_ _-_
    field
      ℂ : Set -- Wondering if this should be a leveled set (i.e. Set₀)

      _+_ : ℂ → ℂ → ℂ
      _-_ : ℂ → ℂ → ℂ
      -_  : ℂ → ℂ
      _*_ : ℂ → ℂ → ℂ

      --+ω : ∀ (N : ℕ) (k : ℕ) → ℂ
      -- Instance arguments seem pretty good https://agda.readthedocs.io/en/v2.5.4/language/instance-arguments.html
      -ω : (N : ℕ) → .⦃ nonZero-n : NonZero N ⦄ → (k : ℕ) → ℂ

      0ℂ  : ℂ
      1ℂ  : ℂ

    open AlgebraStructures  {A = ℂ} _≡_
    open AlgebraDefinitions {A = ℂ} _≡_
    
    field

      +-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0ℂ 1ℂ


      -------------------------------------------------------------------------------
      -- Properties of -ω
      -------------------------------------------------------------------------------

      ω-N-0 : ∀ {N : ℕ} → ⦃ nonZero-n : NonZero N ⦄ → -ω N 0 ≡ 1ℂ

      ω-N-mN : ∀ {N m : ℕ} → ⦃ nonZero-N : NonZero N ⦄ → -ω N (N *ₙ m) ≡ 1ℂ
  
      ω-r₁x-r₁y : 
        ∀ (r₁ x y : ℕ) 
        → ⦃ nonZero-r₁ : NonZero r₁ ⦄
        → ⦃ nonZero-x : NonZero x ⦄ 
        → -ω (r₁ *ₙ x) ⦃ m*n≢0 r₁ x ⦄ (r₁ *ₙ y) ≡ -ω x y

      ω-N-k₀+k₁ : ∀ {N k₀ k₁ : ℕ} → ⦃ nonZero-N : NonZero N ⦄ → -ω N (k₀ +ₙ k₁) ≡ (-ω N k₀) * (-ω N k₁)

