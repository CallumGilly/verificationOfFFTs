module x where

open import Data.Nat
open import Data.Fin

variable
  X Y : Set
  x : X
  n m LANES COMPO : ℕ


--- The most ungenneric version possible
{-
data S₁ : Set where
  ι : ℕ → S₁
  _⊗_ : S₁ → S₁ → S₁

data S₂ : Set where
  ι : S₁ → S₂
  _⊗_ : S₂ → S₂ → S₂

variable
  s₁ s₂ : S₁
  s₃ s₄ : S₂

data P₁ : S₁ → Set where
  ι : Fin n → P₁ (ι n)
  _⊗_ : P₁ s₁ → P₁ s₂ → P₁ (s₁ ⊗ s₂)

data P₂ : S₂ → Set where
  ι : P₁ s₁ → P₂ (ι s₁)
  _⊗_ : P₂ s₃ → P₂ s₄ → P₂ (s₃ ⊗ s₄)
-}



--- Nicest Form
data S (X : Set) : Set where
  ι   : X → S X
  _⊗_ : S X → S X → S X

variable
  s p : S X

data P {f : X → Set} : S X → Set where
  ι : f x → P (ι x)
  _⊗_ : P s → P p → P (s ⊗ p)
  
ar : S X → Set → Set
ar s Y = P s → Y

ufft : ar {S ℕ} (ι (ι 2 ⊗ ι 4) ⊗ s ) Y → ar (ι (ι 2 ⊗ ι 4) ⊗ s) Y


