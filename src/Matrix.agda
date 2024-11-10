module src.Matrix where

open import Data.Nat using (ℕ; _≡ᵇ_; suc; zero; _+_)
open import Data.Fin as F using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Bool using (true; false)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

private
  variable
    n   : ℕ
    X Y : Set

data Shape : Set where
  ι   : ℕ → Shape
  _⊗_ : Shape → Shape → Shape

private
  variable
    s p : Shape

-- Shape to... something
data Position : Shape → Set where
  ι   : Fin n → Position (ι n)
  _⊗_ : Position s → Position p → Position (s ⊗ p)


-- An array takes a shape and a set, and returns a method to access elements of the type of the given set
Ar : Shape → Set → Set
Ar s X = Position s → X

nil : Ar (ι 0) X
nil (ι ())

ι-cons : X → Ar (ι n) X → Ar (ι (suc n)) X
ι-cons x xs (ι  fzero  ) = x
ι-cons x xs (ι (fsuc i)) = xs (ι i)

test : Ar (ι 2) ℕ
test (ι fzero) = 2
test (ι (fsuc x)) = 3

map : (X → Y) → Ar s X → Ar s Y
map f ar i = f (ar i)

-- Define my own version of equality
_==_ : ∀ {s : Shape} {X : Set} → Ar s X → Ar s X → Set
_==_ {s} xs ys = ∀ (p : Position s) → xs p ≡ ys p

-- This is getting stuck because of my use of pattern matching in ι-cons
_ : ι-cons 3 (ι-cons 4 nil) == ι-cons 3 (ι-cons 4 nil)
_ = λ p → refl
-- _ : (map (suc) test) == (ι-cons 4 (ι-cons 5 nil))
-- _ = ?

nest : Ar (s ⊗ p) X → Ar s (Ar p X)
nest a i j = a (i ⊗ j)

unnest : Ar s (Ar p X) → Ar (s ⊗ p) X
unnest a (i ⊗ j) = a i j

transpose : Ar (s ⊗ p) X → Ar (p ⊗ s) X
transpose ar (i ⊗ j) = ar (j ⊗ i)

identityMatrix : ∀ { i : ℕ } → Ar (ι i ⊗ ι i) ℕ
identityMatrix (ι i ⊗ ι j) with (toℕ i) ≡ᵇ (toℕ j)
... | false = 0
... | true  = 1

-- Used AS's paper to give some practive things to make with Matricis
head₁ : Ar (ι (suc n)) X → X
head₁ ar = ar (ι fzero)

tail₁ : Ar (ι (suc n)) X → Ar (ι n) X
tail₁ ar (ι x) = ar (ι (fsuc x))

sum : Ar s ℕ → ℕ
sum = sum′ 0
  where
    sum′ : ∀ {s : Shape} → ℕ → Ar s ℕ → ℕ
    sum′ {ι zero   } n ar = n
    sum′ {ι (suc x)} n ar = sum′ (n + head₁ ar) (tail₁ ar)
    sum′ {s ⊗ s₁   } n ar = sum (map sum (nest ar))

_ : sum (ι-cons 3 (ι-cons 4 nil)) ≡ 7
_ = refl
_ : sum (ι-cons 3 (ι-cons 4 nil)) ≡ 7
_ = refl

_ : ι-cons 3 (ι-cons 4 nil) ≡ ι-cons 3 (ι-cons 4 nil)
_ = refl
_ : sum (unnest (ι-cons (ι-cons 3 (ι-cons 4 nil)) (ι-cons (ι-cons 3 (ι-cons 4 nil)) nil))) ≡ 14
_ = refl

