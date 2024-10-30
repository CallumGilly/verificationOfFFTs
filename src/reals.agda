module src.reals where
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n; _>_; _⊓_)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+; *-comm)

record Real : Set₁ where
  field
    ℝ : Set
    _+ʳ_ : ℝ → ℝ → ℝ
    _-ʳ_ : ℝ → ℝ → ℝ
    _*ʳ_ : ℝ → ℝ → ℝ
    _/ʳ_ : ℝ → ℝ → ℝ

