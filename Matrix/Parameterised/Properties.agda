open import Matrix.Parameterised.Mon

module Matrix.Parameterised.Properties (M : Mon) where

open import Matrix.Parameterised.Base M
open import Matrix.Parameterised.Reshape M
open Mon M

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning
--open Eq.Properties
open import Function
open import Algebra.Definitions

open import Data.Unit
open import Data.Product hiding (swap; map; map₁; map₂; zipWith)


private 
  infixl 4 _⊡_
  _⊡_ = trans

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


map-nest : ∀ (f : X → Y)
           → ∀ (xs : Ar (s ⊗ p) X)
           → ∀ i
           → map f xs i ≡ unnest (map (map f) (nest xs)) i
map-nest f xs (i₁ ⊗ i₂) = refl

map-assoc : ∀ (f : X → Y)
          → ∀ (xs : Ar ((s ⊗ p) ⊗ q) X)
          → ∀ i
          → map f xs i ≡ (reshape assocl
                            (unnest (map (map f) (nest (reshape assocr xs))))
                         ) i
map-assoc f xs i@((i₁ ⊗ i₂) ⊗ i₃) = refl

map-reshape : ∀ (f : X → Y)
            → ∀ (r : Reshape s p)
            → ∀ (xs : Ar s X)
            → ∀ i
            → map f xs i ≡ reshape (rev r) (map f (reshape r xs)) i
map-reshape f r xs i rewrite rev-eq′ r i = refl

reshape-cong  : ∀ (r : Reshape s p)
              → ∀ {a b : Ar s X}
              → (∀ i → a i ≡ b i)
              → ∀ (i : P p) 
              → reshape r a i ≡ reshape r b i
reshape-cong r x i = x (i ⟨ r ⟩)

rev-fact : (r : Reshape s p) → ∀ i j → i ⟨ rev r ⟩ ≡ j → i ≡ j ⟨ r ⟩
rev-fact r i j e = sym (rev-eq′ r i) ⊡ cong (_⟨ r ⟩) e
