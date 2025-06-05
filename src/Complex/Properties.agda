open import src.Real.Base using (RealBase)
open import src.Complex.Base using (CplxBase)

open import Data.Nat.Base using (ℕ) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning

open import Level using (0ℓ) 

module src.Complex.Properties (realBase : RealBase)  (cplxBase : CplxBase realBase) where
  open CplxBase cplxBase
  open import Algebra.Structures {A = ℂ} _≡_
  open import Algebra.Definitions {A = ℂ} _≡_
  record CplxProperties : Set₁ where
    field
      -------------------------------------------------------------------------------
      -- Properties of _+_
      -------------------------------------------------------------------------------

      -- +-identityʳ : ∀ {n : ℂ} → n + (ℂfromℕ 0) ≡ n 
      +-identityʳ : RightIdentity 0ℂ _+_

      -------------------------------------------------------------------------------
      -- Properties of _*_
      -------------------------------------------------------------------------------
      *-comm : Commutative _*_

      --*-identityʳ : ∀ {n : ℂ} → n * (ℂfromℕ 1) ≡ n
      *-identityʳ : RightIdentity 1ℂ _*_

      --*-zeroₗ : ∀ (n : ℂ) → (ℂfromℕ 0) * n ≡ ℂfromℕ 0
      *-zeroˡ : LeftZero 0ℂ _*_


      -------------------------------------------------------------------------------
      -- Structures
      -------------------------------------------------------------------------------

      +-isAbelianGroup : IsAbelianGroup _+_ 0ℂ (-_)

      *-cong           : Congruent₂ _*_
      *-assoc          : Associative _*_
      *-identity       : Identity 1ℂ _*_
      distrib          : _*_ DistributesOver _+_

      isRing : IsRing _+_ _*_ -_ 0ℂ 1ℂ

      +-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0ℂ 1ℂ


      -------------------------------------------------------------------------------
      -- Properties of -ω
      -------------------------------------------------------------------------------

      ω-N-0 : ∀ {N : ℕ} → -ω N 0 ≡ ℂfromℕ 1

      ω-N-mN : ∀ {N m : ℕ} → -ω N (N *ₙ m) ≡ ℂfromℕ 1
  
      ω-r₁x-r₁y : ∀ {r₁ x y : ℕ} → -ω (r₁ *ₙ x) (r₁ *ₙ y) ≡ -ω x y

      -- 99.99% sure that the below is just straight up wrong... (But taken from old complex)
      --ω-multi : ∀ {N₁ N₂ k₁ k₂ : ℕ} → (-ω (N₁ *ₙ N₂) (k₁ *ₙ k₂)) ≡ (-ω N₁ k₁) * (-ω N₂ k₂)

