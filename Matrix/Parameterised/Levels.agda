{-# OPTIONS --allow-unsolved-metas #-}
module Matrix.Parameterised.Levels where

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Fin as Fin hiding (raise; lower)
open import Data.Bool
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning
--open Eq.Properties
open import Function
open import Algebra.Definitions

open import Data.Unit
-- This gives a warn on older versions of Agda when Product doesnt have a zipWith method
open import Data.Product hiding (swap; map; map₁; map₂; zipWith)
open import Data.Product.Properties
open import Data.Sum as Sum hiding (swap; map)

open import Matrix.Mon

private 
  infixl 4 _⊡_
  _⊡_ = trans
-- More powerful lowering and raising
module PL (M : Mon) where
  open import Matrix.Parameterised.Base M
  open import Matrix.Parameterised.Reshape M
  open Mon M

  lower-S : S → U
  lower-S = size

  lower-P : ∀ {s : S} → P s → El (lower-S s)
  lower-P (ι x) = x
  lower-P (i₁ ⊗ i₂) = (Inverse.from $ pair-law _ _) (lower-P i₁ , lower-P i₂)

  raise-P : ∀ {s : S} → El (lower-S s) → P s 
  raise-P {ι x} i = ι i
  raise-P {s ⊗ s₁} i = let x₁ , x₂ = (Inverse.to $ pair-law _ _) i in raise-P x₁ ⊗ raise-P x₂ 

  inv₁ : ∀ {s : S} → (i : P s) → raise-P (lower-P i) ≡ i
  inv₁ {ι _} (ι _) = refl
  inv₁ {s₁ ⊗ s₂} (i₁ ⊗ i₂) = let
      inverse₁ = 
        Inverse.inverse 
          (pair-law (lower-S s₁) (lower-S s₂)) 
          .proj₁ 
          {lower-P i₁ , lower-P i₂} 
          {lower-P {s₁ ⊗ s₂} (i₁ ⊗ i₂)} 
          refl 
      left  = ,-injectiveˡ inverse₁
      right = ,-injectiveʳ inverse₁
      in 
      (cong₂ _⊗_) (cong raise-P left ⊡ inv₁ i₁) (cong raise-P right ⊡ inv₁ i₂)

  inv₂ : ∀ {s : S} → (i : El (lower-S s)) → lower-P {s} (raise-P i) ≡ i
  inv₂ {ι x} i = refl
  inv₂ {s₁ ⊗ s₂} i = 
      let
        i₁ , i₂ = Inverse.to (pair-law (lower-S s₁) (lower-S s₂)) i
        inverse₂ = 
          Inverse.inverse 
            (pair-law (lower-S s₁) (lower-S s₂)) 
            .proj₂ 
            {i}
            {i₁ , i₂} 
            refl
      in 
          cong 
            (Inverse.from (pair-law (lower-S s₁) (lower-S s₂))) 
            (cong₂ _,_ (inv₂ {s₁} i₁) (inv₂ {s₂} i₂)) 
        ⊡ inverse₂
  
  lower-Ar : ∀ {s : S} → ∀ {X : Set} → Ar s X → El (lower-S s) → X
  lower-Ar xs = xs ∘ raise-P 

  raise-Ar : ∀ {s : S} → ∀ {X : Set} → (El (lower-S s) → X) → Ar s X
  raise-Ar xs = xs ∘ lower-P

module PLR (M : Mon) where
  open Mon M
  open import Matrix.Parameterised.Base M
  open import Matrix.Parameterised.Reshape M
  open PL M

  data ℓ : Set where
    uu ss : ℓ

  Sℓ : ℓ -> Set
  Sℓ uu = U
  Sℓ ss = S

  Pℓ : ∀ {s : ℓ} → Sℓ s -> Set
  Pℓ {s = uu} = El
  Pℓ {s = ss} = P

  infixl 5 _∙_
  data Reshapeℓ : {a b : ℓ} → Sℓ a → Sℓ b → Set₁ where
    resh-S : ∀ {s p : S} → (r : Reshape s p) → Reshapeℓ {ss} {ss} s p
    --resh-U : ∀ {s   : U} (r : Σ (U → U) (λ f → ∀ {u : U} → El u → El (f u) )) → Reshapeℓ {uu} {uu} (r .proj₁ s) s
    -- Don't like the below solution - as it doesn't allow the parsing of a Reshapeℓ
    resh-U : ∀ {s p : U} → {rshp : RShp U El} → (r : RShp.Reshape rshp s p) → Reshapeℓ {uu} {uu} s p
    raise  : ∀ {s   : S} → Reshapeℓ {ss} {uu} s (lower-S s)
    lower  : ∀ {s   : S} → Reshapeℓ {uu} {ss} (lower-S s) s
    eq     : ∀ {a : ℓ}  {su  : Sℓ a} → Reshapeℓ {a} {a} su su
    _∙_    : ∀ {s p q : ℓ} 
           → ∀ {su : Sℓ s} 
           → ∀ {pu : Sℓ p}
           → ∀ {qu : Sℓ q} 
           → Reshapeℓ {s} {p} su pu → Reshapeℓ {q} {s} qu su → Reshapeℓ {q} {p} qu pu 
{-
    _⊕_    : ∀ {su₁ su₂ pu₁ pu₂ : Sℓ ss} 
           → Reshapeℓ {?} {?} su₁ pu₁ → Reshapeℓ {?} {?} su₂ pu₂
           → Reshapeℓ {?} {?} (su₁ ⊗ su₂) (pu₁ ⊗ pu₂)
-}

  _⟨_⟩ₗ : ∀ {a b : ℓ} {s : Sℓ a} {p : Sℓ b} → Pℓ {b} p → Reshapeℓ {a} {b} s p → Pℓ {a} s
  i ⟨ eq       ⟩ₗ = i
  i ⟨ r₁ ∙ r₂  ⟩ₗ = (i ⟨ r₁ ⟩ₗ) ⟨ r₂ ⟩ₗ
  i ⟨ resh-S r ⟩ₗ = i ⟨ r ⟩ 
  i ⟨ resh-U {rshp = rshp} r ⟩ₗ = RShp._⟨_⟩ rshp i r
  i ⟨ raise    ⟩ₗ = raise-P i
  i ⟨ lower    ⟩ₗ = lower-P i

  revℓ : ∀ {a b : ℓ} → ∀ {s : Sℓ a} {p : Sℓ b} → Reshapeℓ {a} {b} s p → Reshapeℓ {b} {a} p s
  revℓ {_} {_} {s} {.s} eq = eq
  revℓ {_} {_} {s} {p} (r₁ ∙ r₂) = (revℓ r₂) ∙ (revℓ r₁)
  revℓ {_} {_} {s} {p} (resh-U r) = ?
  revℓ {_} {_} {.(_)} {.(_)} (resh-S r) = resh-S (rev r)
  revℓ {_} {_} {s} {.((lower-S s))} raise = lower
  revℓ {_} {_} {.((lower-S s))} {s} lower = raise

  rev-eq′ℓ : ∀ {a b : ℓ} 
           → ∀ {s : Sℓ a} 
           → ∀ {q : Sℓ b} 
           → ∀ (r : Reshapeℓ {a} {b} s q)
           → ∀ (i : Pℓ {a} s) 
           → i ⟨ revℓ {a} {b} {s} {q}  r ∙ r ⟩ₗ ≡ i
  rev-eq′ℓ {_} {_} {s} {.s} eq i = refl
  rev-eq′ℓ {_} {_} {s} {q} (r ∙ r₁) i rewrite 
      rev-eq′ℓ r (i ⟨ revℓ r₁ ⟩ₗ) 
    | rev-eq′ℓ r₁ i 
    = refl
  rev-eq′ℓ {_} {_} {(s)} {.(_)} (resh-S r) i rewrite rev-eq′ r i = refl
  rev-eq′ℓ {_} {_} {s} {p} (resh-U r) = ?
  rev-eq′ℓ {_} {_} {(s)} {.((lower-S s))} raise i = inv₁ i
  rev-eq′ℓ {_} {_} {.((lower-S s))} {(s)} lower i = inv₂ {s} i

