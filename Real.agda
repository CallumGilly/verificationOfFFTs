module Real where

  open import Data.Nat.Base using (ℕ) renaming (_*_ to _*ₙ_)

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym)
  open Eq.≡-Reasoning

  import Algebra.Structures as AlgebraStructures
  import Algebra.Definitions as AlgebraDefinitions

  record Real : Set₁ where

    infix  9 _ᵣ
    infixr 8 -_
    infixl 7 _*_ _/_
    infixl 6 _+_ _-_

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

    0ℝ  : ℝ
    0ℝ  = (0 ᵣ)
    -1ℝ : ℝ
    -1ℝ = (- (1 ᵣ))
    1ℝ  : ℝ
    1ℝ  = (1 ᵣ)

    open AlgebraStructures  {A = ℝ} _≡_
    open AlgebraDefinitions {A = ℝ} _≡_

    field
      +-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0ℝ 1ℝ
      0/N≡0 : ∀ (N : ℝ) → 0ℝ / N ≡ 0ℝ

      cos0  : cos 0ℝ ≡ 1ℝ
      sin0  : sin 0ℝ ≡ 0ℝ

      cos-2πn : ∀ (n : ℕ) → cos ((- (2 ᵣ * π)) * (n ᵣ)) ≡ 1ℝ
      sin-2πn : ∀ (n : ℕ) → sin ((- (2 ᵣ * π)) * (n ᵣ)) ≡ 0ℝ

      ᵣ-distrib-* : ∀ (n m : ℕ) → (n *ₙ m) ᵣ ≡ (n ᵣ) * (m ᵣ)
      -distrib-* : ∀ (n m : ℝ) → (- n) * m ≡ - (n * m)

      Nm/N≡m : ∀ (N m : ℝ) → (N * m) / N ≡ m

      --double-negative : ∀ (x : ℝ) → - (- x) ≡ x

      --*-comm : Commutative _*_
      --*-identityˡ : LeftIdentity  1ℝ _*_
      --*-identityʳ : RightIdentity 1ℝ _*_
      --*-zeroˡ     : LeftZero  0ℝ _*_
      --*-zeroʳ     : RightZero 0ℝ _*_
      --*ᵣ-assoc    : Associative _*_

--    -- /ᵣ-zeroₜ : ∀ (x : ℝ) → (0 ᵣ) / x  ≡ 0 ᵣ

      --+-comm      : Commutative _+_
      --+-identityˡ : LeftIdentity  0ℝ _+_
      --+-identityʳ : RightIdentity 0ℝ _+_
      --+-assoc     : Associative _+_

--    -- -ᵣ-identityʳ : ∀ (x : ℝ) → x - (0 ᵣ) ≡ x

--    -- neg-distrib-* : ∀ (x y : ℝ) → (- x) * y ≡ - (x * y)
--    -- *-cancels-/ : ∀ (x y : ℝ) → x * (y / x) ≡ y
