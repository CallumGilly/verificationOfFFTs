open import Matrix.Mon

module Matrix.Leveled.Change-Major (M : Mon) where
open Mon M
open import Matrix.Leveled.Base M
open import Matrix.Leveled.Reshape M

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning

private
  variable 
    l : L
    X : Set
  
v-eq : ∀ (u₁ u₂ : U) → (u₁ ≡ u₂) → P (ν u₁) → P (ν u₂)
v-eq u₁ u₂ refl a = a

u-flattenᵗ : ∀ {s : S l} → u-flatten s ≡ u-flatten (transp s)
u-flattenᵗ {_} {ν x} = refl
u-flattenᵗ {_} {ι s} = refl
u-flattenᵗ {_} {s₁ ⊗ s₂} rewrite
    u-flattenᵗ {_} {s₁} 
  | u-flattenᵗ {_} {s₂} 
  = comm 

record CM : Set₁ where
  field 
    change-majorᵣ : ∀ {s : S l} → Reshape (transp s) s
    preserves-flat : ∀ {s : S l} 
                   → ∀ (xs : Ar s X) 
                   → ∀ (i : P (ν (u-flatten s))) 
                   → (reshape u-flattenᵣ xs) i 
                   ≡ (reshape (u-flattenᵣ ∙ (rev change-majorᵣ)) xs) (v-eq (u-flatten s) (u-flatten (transp s)) (u-flattenᵗ {_} {s}) i)

