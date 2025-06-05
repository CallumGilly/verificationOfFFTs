open import src.Real using (Real)

open import Data.Nat.Base using (ℕ) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning

module src.Complex (real : Real) where
  open Real real using (ℝ; 0ℝ; 1ℝ; -1ℝ)

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

      fromℝ : ℝ → ℂ

      e^i_ : ℝ → ℂ
      ℂ-conjugate : ℂ → ℂ

      --+ω : ∀ (N : ℕ) (k : ℕ) → ℂ
      -ω : (N : ℕ) → (k : ℕ) → ℂ


    0ℂ  : ℂ
    0ℂ  = fromℝ (0ℝ)
    -1ℂ : ℂ
    -1ℂ = fromℝ (-1ℝ)
    1ℂ  : ℂ
    1ℂ  = fromℝ (1ℝ)

    open AlgebraStructures  {A = ℂ} _≡_
    open AlgebraDefinitions {A = ℂ} _≡_
    
    field

      +-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0ℂ 1ℂ


      -------------------------------------------------------------------------------
      -- Properties of -ω
      -------------------------------------------------------------------------------

      ω-N-0 : ∀ {N : ℕ} → -ω N 0 ≡ 1ℂ

      ω-N-mN : ∀ {N m : ℕ} → -ω N (N *ₙ m) ≡ 1ℂ
  
      ω-r₁x-r₁y : ∀ {r₁ x y : ℕ} → -ω (r₁ *ₙ x) (r₁ *ₙ y) ≡ -ω x y

      -- 99.99% sure that the below is just straight up wrong... (But taken from old complex)
      --ω-multi : ∀ {N₁ N₂ k₁ k₂ : ℕ} → (-ω (N₁ *ₙ N₂) (k₁ *ₙ k₂)) ≡ (-ω N₁ k₁) * (-ω N₂ k₂)

