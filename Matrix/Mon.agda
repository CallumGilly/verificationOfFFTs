module Matrix.Mon where

open import Function
open import Algebra.Definitions
open import Data.Unit
open import Data.Product 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)

record Mon : Set₁ where
  field
    U : Set
    El : U → Set

    ε : U
    _●_ : U → U → U

    unit-law : El ε ↔ ⊤
    -- -- The bracketing on the left hand side here is VERY important, otherwise
    -- -- we have a pair where the left is an isomorhism... that took me too long
    pair-law : ∀ a b → El (a ● b) ↔ (El a × El b)
    
    -- This does restrict out ability to use ⊗ as ●, but I think thats okay with Levels 
    comm : ∀ {u₁ u₂ : U} → (u₁ ● u₂) ≡ (u₂ ● u₁)
