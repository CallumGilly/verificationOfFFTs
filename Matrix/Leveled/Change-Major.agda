open import Matrix.Mon

module Matrix.Leveled.Change-Major (M : Mon) where
open Mon M
open import Matrix.Leveled.Base M
open import Matrix.Leveled.Reshape M
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning

private
  variable 
    l : L
    X : Set
  
record Change-Major : Set₁ where
  field
    BaseCM : ∀ {s p : S (ss zz)} → Reshape (ν (u-flatten-z (flatten-z s) ● u-flatten-z (flatten-z p))) (ν (u-flatten-z (flatten-z p) ● u-flatten-z (flatten-z s)))
    
  CM : ∀ {s p : S (ss l)} → Reshape (s ⊗ p) (p ⊗ s)
  CM {zz  } {s} {p} = (rev flatten-zᵣ) 
                    ∙ BaseCM {s} {p}
                    ∙ flatten-zᵣ
  CM {ss l} {s} {p} = (rev flatten-zᵣ) 
                    ∙ CM {l}
                    ∙ flatten-zᵣ


  CMᵗ : ∀ {s : S l} → Reshape (transp s) s
  CMᵗ {.zz} {ν x} = eq
  CMᵗ {.(ss _)} {ι s} = eq
  CMᵗ {.(ss _)} {s ⊗ s₁} = CMᵗ ⊕ CMᵗ ∙ CM


--tm : Change-Major
--Change-Major.BaseCM tm = subst (λ t → Reshape ? ?) refl eq 

{-
ν-eq : ∀ (u₁ u₂ : U) → (u₁ ≡ u₂) → P (ι (ν u₁)) → P (ι (ν u₂))
ν-eq u₁ u₂ refl a = a

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
    preserves-flat : ∀ {s : S (ss l)} 
                   → ∀ (xs : Ar s X) 
                   → ∀ (i : P (ι (ν (u-flatten s))))
                   → reshape u-flattenᵣ xs i 
                   ≡ reshape (u-flattenᵣ ∙ (rev change-majorᵣ)) xs 
                          (ν-eq (u-flatten s) (u-flatten (transp s)) (u-flattenᵗ {_} {s}) i)
    single-level : ∀ {l : L} → ∀ {s : S l} → ∀ (i : P s) → (ι i) ⟨ change-majorᵣ ⟩ ≡ ι i

-}
    {-
    helper : ∀ {s : S l}
           → (xs ys : Ar (transp s) X)
           → (prf : ∀ (i : P s) → reshape transpᵣ xs i ≡ reshape transpᵣ ys i)
           → reshape change-majorᵣ xs i ≡ reshape change-majorᵣ ys i
    helper : ∀ {s : S (ss l)}
       → ∀ {dft : {s : S l} → Ar s ℂ → Ar s ℂ}
       → ∀ {twid : ∀ {lv : L} → ∀ {s p : S (ss lv)} → P s → P p → ℂ}
       → ∀ (r : Reshape {ss l} {ss l} (transp s) s)
       → (xs : Ar s ℂ)
       → (i : P s)
       → fft {l} dft twid {s} xs (i ⟨ transpᵣ ⟩)
       ≡ fft {l} dft twid {s} xs (i ⟨ r ⟩)
    -}

