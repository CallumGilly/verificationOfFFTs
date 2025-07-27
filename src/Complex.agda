open import src.Real using (Real)

open import Data.Nat.Base using (ℕ; NonZero; suc) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties using (m*n≢0)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning

open import Data.Product.Base using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

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
      -- Instance arguments seem pretty good https://agda.readthedocs.io/en/v2.5.4/language/instance-arguments.html
      -ω : (N : ℕ) → .(prf : NonZero N) → (k : ℕ) → ℂ


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

      ω-N-0 : ∀ {N : ℕ} → (prf : NonZero N) → -ω N prf 0 ≡ 1ℂ

      ω-N-mN : ∀ {N m : ℕ} → (prf : NonZero N) → -ω N prf (N *ₙ m) ≡ 1ℂ
  
      ω-r₁x-r₁y : 
        ∀ (r₁ x y : ℕ) 
        → (nonZero-r₁ : NonZero r₁) 
        → (nonZero-x : NonZero x) 
        → -ω (r₁ *ₙ x) (m*n≢0 r₁ x {{nonZero-r₁}} {{nonZero-x}} ) (r₁ *ₙ y) ≡ -ω x nonZero-x y

      ω-N-k₀+k₁ : ∀ {N k₀ k₁ : ℕ} → (prf : NonZero N) → -ω N prf (k₀ +ₙ k₁) ≡ (-ω N prf k₀) * (-ω N prf k₁)

