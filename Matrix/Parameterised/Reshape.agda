{-# OPTIONS --allow-unsolved-metas #-}
 
open import Matrix.Parameterised.Mon 

module Matrix.Parameterised.Reshape (M : Mon) where

open import Matrix.Parameterised.Base M

open Mon M

private 
  variable
    s p q r : S
    m n : U
    X Y Z : Set

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning
--open Eq.Properties
open import Function
open import Algebra.Definitions

open import Data.Unit
open import Data.Product hiding (swap; map; map₁; map₂; zipWith)

record RShp (S : Set) (P : S → Set) : Set₁ where
  field
    Reshape : S → S → Set
    _∙_ : ∀ {s p q : S} → Reshape p q → Reshape s p → Reshape s q 
    _⟨_⟩ : ∀ {s p : S} → P s → Reshape p s → P p
    rev : ∀ {s p : S} → Reshape s p → Reshape p s
    rev-eq : ∀ {s p : S} 
            → ∀ (r : Reshape s p) 
            → ∀ (i : P p) 
            →  i ⟨ r ∙ rev r ⟩ ≡ i 
    rev-rev : ∀ {s p : S}
            → ∀ (r : Reshape s p)
            → ∀ (i : P p ) → 
            i ⟨ rev (rev r) ⟩ ≡ i ⟨ r ⟩

infixl 5 _∙_
data Reshape : S → S → Set where
  eq : Reshape s s
  _⊕_ : Reshape s p → Reshape q r → Reshape (s ⊗ q) (p ⊗ r)
  _∙_ : Reshape p q → Reshape s p → Reshape s q
  swap : Reshape (s ⊗ p) (p ⊗ s)
  assocl : Reshape (s ⊗ (p ⊗ q)) ((s ⊗ p) ⊗ q)
  assocr : Reshape ((s ⊗ p) ⊗ q) (s ⊗ (p ⊗ q))
  
  flat   : Reshape (ι n ⊗ ι m) (ι (n ● m))
  unflat : Reshape (ι (n ● m)) (ι n ⊗ ι m)

_⟨_⟩ : P s → Reshape p s → P p
i ⟨ eq ⟩ = i
(i ⊗ i₁) ⟨ r ⊕ r₁ ⟩ = (i ⟨ r ⟩) ⊗ (i₁ ⟨ r₁ ⟩)
i ⟨ r ∙ r₁ ⟩ = (i ⟨ r ⟩) ⟨ r₁ ⟩
(i ⊗ i₁) ⟨ swap ⟩ = i₁ ⊗ i
((i ⊗ j) ⊗ k) ⟨ assocl ⟩ = i ⊗ (j ⊗ k)
(i ⊗ (j ⊗ k)) ⟨ assocr ⟩ = (i ⊗ j) ⊗ k
ι x ⟨ flat ⟩ = let a = (Inverse.to $ pair-law _ _) x 
               in ι (proj₁ a) ⊗ ι (proj₂ a) 
(ι x₁ ⊗ ι x₂) ⟨ unflat ⟩ =  ι ((Inverse.from $ pair-law _ _) (x₁ , x₂))

rev : Reshape s p → Reshape p s
rev eq = eq
rev (r₁ ⊕ r₂) = (rev r₁) ⊕ (rev r₂)
rev (r₁ ∙ r₂) = (rev r₂) ∙ (rev r₁)
rev swap = swap
rev assocl = assocr
rev assocr = assocl
rev flat = unflat
rev unflat = flat

rev-rev : ∀ (r : Reshape s p) (i : P p ) → i ⟨ rev (rev r) ⟩ ≡ i ⟨ r ⟩
rev-rev eq i = refl
rev-rev (r ⊕ r₁) i = ?
rev-rev (r ∙ r₁) i = ?
rev-rev swap i = ?
rev-rev assocl i = ?
rev-rev assocr i = ?
rev-rev flat i = ?
rev-rev unflat i = ?

rev-eq : ∀ (r : Reshape s p) (i : P p) →  i ⟨ r ∙ rev r ⟩ ≡ i
rev-eq eq i = refl
rev-eq (r₁ ⊕ r₂) (i₁ ⊗ i₂) rewrite rev-eq r₁ i₁ | rev-eq r₂ i₂ = refl
rev-eq (r₁ ∙ r₂) i rewrite rev-eq r₂ (i ⟨ r₁ ⟩) | rev-eq r₁ i  = refl
rev-eq swap (i₁ ⊗ i₂) = refl
rev-eq assocl (i₁ ⊗ i₂ ⊗ i₃) = refl
rev-eq assocr (i₁ ⊗ (i₂ ⊗ i₃)) = refl
rev-eq flat i = ?
rev-eq unflat i = ?

reshape-is-RShp : RShp S P
reshape-is-RShp = record
  { Reshape = Reshape
  ; _∙_     = _∙_
  ; _⟨_⟩    = _⟨_⟩
  ; rev     = rev
  ; rev-eq  = rev-eq
  ; rev-rev = rev-rev
  }

rev-eq′ : ∀ (r : Reshape s p) (i : P s) →  i ⟨ rev r ∙ r ⟩ ≡ i
rev-eq′ r i rewrite
    sym (rev-rev r (i ⟨ rev r ⟩))
  = rev-eq (rev r) i 

reshape : Reshape s p → Ar s X → Ar p X
reshape r a i = a (i ⟨ r ⟩)

transp : S → S
transp (ι n) = ι n
transp (s ⊗ p) = transp p ⊗ transp s

transpᵣ : Reshape (transp s) s
transpᵣ {ι x} = eq
transpᵣ {s ⊗ s₁} = (transpᵣ ⊕ transpᵣ) ∙ swap

size : S → U
size (ι x) = x
size (s₁ ⊗ s₂) = size s₁ ● size s₂

flatten : Reshape s (ι (size s))
flatten {ι x} = eq
flatten {s₁ ⊗ s₂} = flat ∙ flatten ⊕ flatten

unflatten : Reshape (ι (size s)) s 
unflatten = rev flatten


