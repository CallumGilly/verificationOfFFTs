module src.Real.Base where

open import Data.Nat.Base using (ℕ)

record RealBase : Set₁ where

  infix  9 _ᵣ
  infixr 8 -_
  infixl 7 _*_ _/_
  infixl 6 _+_ _-_

  field
    ℝ : Set

    0ℝ  : ℝ
    -1ℝ : ℝ
    1ℝ  : ℝ

    _ᵣ :    ℕ → ℝ
    π    : ℝ

    _+_ : ℝ → ℝ → ℝ
    _-_ : ℝ → ℝ → ℝ
    _*_ : ℝ → ℝ → ℝ
    _/_ : ℝ → ℝ → ℝ
    -_ : ℝ → ℝ

    cos : ℝ → ℝ
    sin : ℝ → ℝ
