open import Matrix.Parameterised.Mon

module Matrix.Parameterised.Base (M : Mon) where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning
--open Eq.Properties
open import Function
open import Algebra.Definitions

open import Data.Unit
open import Data.Product hiding (swap; map; map₁; map₂; zipWith)



open Mon M

infixl 15 _⊗_
data S : Set where
  ι : U → S  --  ι n means ι (suc n)
  _⊗_ : S → S → S

private 
  infixl 4 _⊡_
  _⊡_ = trans

  variable
    s p : S
    n : U
    X Y Z : Set

data P : S → Set where
  ι : El n → P (ι n)
  _⊗_ : P s → P p → P (s ⊗ p)

Ar : S → Set → Set
Ar s X = P s → X

map : (X → Y) → Ar s X → Ar s Y
map f a i = f (a i)

imap : (P s → X → Y) → Ar s X → Ar s Y
imap f a i = f i (a i)

zipWith : (X → Y → Z) → Ar s X → Ar s Y → Ar s Z
zipWith _⊡_ a b i = a i ⊡ b i

nest : Ar (s ⊗ p) X → Ar s (Ar p X)
nest a i j = a (i ⊗ j)

unnest : Ar s (Ar p X) → Ar (s ⊗ p) X
unnest a (i ⊗ j) = a i j
