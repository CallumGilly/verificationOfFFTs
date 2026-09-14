{-# OPTIONS --allow-unsolved-metas #-}
module Matrix.SimpleLeveledRelation where


open import Matrix.Simple.Base as Spl
open import Matrix.Simple.NonZero

open import Matrix.Mon
open import Matrix.NatMon
open import Matrix.Leveled.Base ℕ-Mon as Lvl

open import Data.Nat.Base
open import Data.Product

open import Function.Bundles
open Inverse

open import Relation.Binary.PropositionalEquality

-- Σ-≡-intro is taken from https://stackoverflow.com/a/37492419 , András Kovács under CC BY-SA 3.0
Σ-≡-intro :
  ∀ {α β}{A : Set α}{B : A → Set β}{a a' : A}{b : B a}{b' : B a'}
  → (Σ (a ≡ a') λ p → subst B p b ≡ b') → (a , b) ≡ (a' , b')
Σ-≡-intro (refl , refl) = refl

module Shp where
  -- This may be messed up by nonZero
  to′ : Σ Shape NonZeroₛ → S (ss zz)
  to′ (ι (suc n) , ι _) = ι (ν n)
  to′ ((s₁ ⊗ s₂) , (nz₁ ⊗ nz₂)) = (to′ (s₁ , nz₁)) ⊗ (to′ (s₂ , nz₂))

  from′ : S (ss zz) → Σ Shape NonZeroₛ 
  from′ (ι (ν n)) = ι (suc n) , ι nonZero
  from′ (s₁ ⊗ s₂) = from′ s₁ .proj₁ ⊗ from′ s₂ .proj₁ , from′ s₁ .proj₂ ⊗ from′ s₂ .proj₂

  inverse₁ : ∀ (s : S (ss zz)) → to′ (from′ s) ≡ s
  inverse₁ (ι (ν _)) = refl
  inverse₁ (s₁ ⊗ s₂) rewrite inverse₁ s₁ | inverse₁ s₂ = refl

  private
    lemma₁ : ∀ {s₁} {nz₁ : NonZeroₛ s₁} →
         from′ (to′ (s₁ , nz₁)) .proj₁ ≡ s₁
    lemma₁ {ι zero} {ι ()}
    lemma₁ {ι (suc x)} {ι x₁} = refl
    lemma₁ {s₁ ⊗ s₂} {nz₁ ⊗ nz₂} = cong₂ _⊗_ lemma₁ lemma₁

  {-# TERMINATING #-}
  inverse₂ : ∀ (s : Σ Shape NonZeroₛ) → from′ (to′ s) ≡ s
  inverse₂ (ι (suc _) , ι _) = refl
  inverse₂ ((s₁ ⊗ s₂) , (nz₁ ⊗ nz₂)) rewrite 
      inverse₂ (s₁ , nz₁) 
    | inverse₂ (s₂ , nz₂) = refl

  --dcong₂ _,_ (cong₂ _⊗_ lemma₁ lemma₁) ?

  iso : Σ Shape NonZeroₛ ↔ S (ss zz)
  iso .to = to′
  iso .from = from′
  iso .to-cong refl = refl
  iso .from-cong refl = refl
  iso .inverse .proj₁ refl = inverse₁ _
  iso .inverse .proj₂ refl = inverse₂ _ 

open Shp using () renaming (to′ to S-to; from′ to S-from; inverse₁ to S-inverse₁; inverse₂ to S-inverse₂; iso to S-iso) public 
 
module Pos where
  to′ : ∀ {s : Σ Shape NonZeroₛ} → Position (s .proj₁) → P (S-to s)
  to′ {ι (suc n) , ι x} (ι i) = ι (ν i)
  to′ {s₁ ⊗ s₂ , nz₁ ⊗ nz₂} (i₁ ⊗ i₂) = to′ i₁ ⊗ to′ i₂

  from′ : ∀ {s : S (ss zz)} → P s → Position (S-from s .proj₁)
  from′ {ι (ν n)} (ι (ν i)) = ι i
  from′ {s₁ ⊗ s₂} (i₁ ⊗ i₂) = from′ i₁ ⊗ from′ i₂

  inverse₁ : ∀ {s : S (ss zz)} → (i : P s) → subst P (S-inverse₁ s) (to′ (from′ i)) ≡ i --subst P (sym (S-inverse₁ s)) i
  inverse₁ {ι (ν n)} (ι (ν i)) = refl
  inverse₁ {s₁ ⊗ s₂} (i₁ ⊗ i₂) with S-inverse₁ s₁ 
  ... | a = ?

  inverse₂ : ∀ {s : Σ Shape NonZeroₛ} → (i : Position (s .proj₁)) → subst Position (cong proj₁ (S-inverse₂ s)) (from′ (to′ i)) ≡ i
  inverse₂ {ι (suc n) , ι _} (ι i) = refl
  inverse₂ {s₁ ⊗ s₂ , nz₁ ⊗ nz₂} (i₁ ⊗ i₂) = ?

open Pos using () renaming (to′ to P-to; from′ to P-from; inverse₁ to P-inverse₁; inverse₂ to P-inverse₂) public

module Ars where
  lemma₁ : ∀ {s : Σ Shape NonZeroₛ}
         → S-from (S-to s) .proj₁ ≡ s .proj₁
  lemma₁ {fst , snd} = ?

  to′ : ∀ {X : Set} {s : Σ Shape NonZeroₛ} → Spl.Ar (s .proj₁) X → Lvl.Ar (S-to s) X
  to′ {_} {fst , snd} xs j = let j′ = subst Position lemma₁ (P-from j) in xs j′ 

  from′ : ∀ {X : Set} {s : S (ss zz)} → Lvl.Ar s X → Spl.Ar (S-from s .proj₁) X
  from′ {X} {s} xs j = let j′ = subst P (S-inverse₁ s) (P-to j) in xs (j′)

open Ars using () renaming (to′ to Ar-to; from′ to Ar-from) public



