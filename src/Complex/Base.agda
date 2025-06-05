
open import src.Real.Base using (RealBase)

open import Data.Nat.Base using (ℕ)



module src.Complex.Base (realBase : RealBase) where
  open RealBase realBase using (ℝ)

  record CplxBase : Set₁ where
    infix  8 -_
    infixl 7 _*_
    infixl 6 _+_ _-_
    field
      ℂ : Set -- Wondering if this should be a leveled set (i.e. Set₀)

      0ℂ  : ℂ
      -1ℂ : ℂ
      1ℂ  : ℂ

      _+_ : ℂ → ℂ → ℂ
      _-_ : ℂ → ℂ → ℂ
      -_  : ℂ → ℂ
      _*_ : ℂ → ℂ → ℂ

      fromℝ : ℝ → ℂ
      ℂfromℕ : ℕ → ℂ

      e^i_ : ℝ → ℂ
      ℂ-conjugate : ℂ → ℂ

      +ω : ∀ (N : ℕ) (k : ℕ) → ℂ
      -ω : ∀ (N : ℕ) (k : ℕ) → ℂ


