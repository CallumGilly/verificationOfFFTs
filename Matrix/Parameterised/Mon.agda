module Matrix.Parameterised.Mon where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning
--open Eq.Properties
open import Function
open import Algebra.Definitions

open import Data.Unit
open import Data.Product hiding (swap; map; map₁; map₂; zipWith)

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
