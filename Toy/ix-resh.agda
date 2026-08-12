module Toy.ix-resh where
open import Data.Nat

module _ where
  data L : Set where
    lzero : L
    lsucc : L → L

  variable 
    l l₁ l₂ : L

  data S : L → Set where
    ν : ℕ → S lzero
    ι : S l → S (lsucc l)
    _⊗_ : S l → S l → S l

  variable
    s s₁ s₂ : S l

  _●_ = _*_
  
  data R : S l₁ → S l₂ → Set where
    flat   : ∀ {m n} → R (ι (ν m) ⊗ ι (ν n)) (ν (m ● n))
    unflat : ∀ {m n} → R (ν (m ● n)) (ι (ν m) ⊗ ι (ν n))

module CurrentIx where

  open import Data.String
  open import Text.Printf

  data Ix : S l → Set where
    ν : {n : ℕ} → String → Ix (ν n)
    ι : Ix s → Ix (ι s)
    _⊗_ : Ix s₁ → Ix s₂ → Ix (s₁ ⊗ s₂)
  
  resh-ix : R s₁ s₂ → Ix s₁ → Ix s₂
  resh-ix (flat {m} {n}) (ι (ν i₁) ⊗ ι (ν i₂)) = ν (printf "(%s * %u) + %s" i₁ n i₂)
  resh-ix (unflat {m} {n}) (ν x) = ι (ν "x / m") ⊗ ι (ν "x % m") -- or something like that
  
  -- This is "difficult" to work with (requires actual thinking ergo could introduce errors)

module NewIx where
  
  open import Data.String

  data Math : Set where
    Var : String → Math
    _/′_ : Math → Math → Math
    _%′_ : Math → Math → Math
    _*′_ : Math → Math → Math
    _+′_ : Math → Math → Math

  data Ix : S l → Set where
    ν : {n : ℕ} → Math → Ix (ν n)
    ι : Ix s → Ix (ι s)
    _⊗_ : Ix s₁ → Ix s₂ → Ix (s₁ ⊗ s₂)
  
  resh-ix : R s₁ s₂ → Ix s₁ → Ix s₂

  -- Such that we can then give some reduction rules to _*_ and _/_ and verify 
  -- that flat ∙ unflat works as expected
