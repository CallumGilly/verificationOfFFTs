module Matrix.Simple.SubShape where

open import Matrix.Simple.Base
open import Matrix.Simple.Reshape

open import Data.Maybe

private variable
  s s₁ s₂ q q₁ q₂ : Shape

data _⊂_ : Shape → Shape → Set
data _⊆_ : Shape → Shape → Set

data _⊆_ where
  idh : s ⊆ s
  srt : q ⊂ s → q ⊆ s 

data _⊂_ where
  left  : q  ⊆ s₁ → q  ⊂ (s₁ ⊗ s₂)
  right : q  ⊆ s₂ → q  ⊂ (s₁ ⊗ s₂)
  bothₗ : q₁ ⊂ s₁ → q₂ ⊆ s₂ → (q₁ ⊗ q₂) ⊂ (s₁ ⊗ s₂) 
  bothᵣ : q₁ ⊆ s₁ → q₂ ⊂ s₂ → (q₁ ⊗ q₂) ⊂ (s₁ ⊗ s₂)

--- Properties

inv-⊂ : q ⊂ s → Shape
inv-⊆ : q ⊆ s → Maybe Shape

inv-⊆ {s} idh = nothing
inv-⊆ (srt x) = just (inv-⊂ x)

inv-⊂ (left  {s₂ = s₂} s⊆q) with inv-⊆ s⊆q
... | just x  = x ⊗ s₂
... | nothing = s₂
inv-⊂ (right {s₁ = s₁} q⊆p) with inv-⊆ q⊆p
... | just x  = s₁ ⊗ x
... | nothing = s₁
inv-⊂ (bothₗ q₁⊂s₁ q₂⊆s₂)   with inv-⊂ q₁⊂s₁ | inv-⊆ q₂⊆s₂
... | x | just y  = x ⊗ y
... | x | nothing = x
inv-⊂ (bothᵣ q₁⊆s₁ q₂⊂s₂)   with inv-⊆ q₁⊆s₁ | inv-⊂ q₂⊂s₂
... | just x  | y = x ⊗ y
... | nothing | y =     y



