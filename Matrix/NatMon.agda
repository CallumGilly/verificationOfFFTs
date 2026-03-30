{-# OPTIONS --allow-unsolved-metas #-}
module Matrix.NatMon where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning
open import Function
open import Algebra.Definitions

open import Data.Unit
open import Data.Fin hiding (_+_)
open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Product hiding (swap; map; map₁; map₂; zipWith)

open import Matrix.Mon
import Data.Fin as Fin
open import Data.Fin.Properties
open import Function.Bundles
open Inverse
open import Data.Nat.Solver
open +-*-Solver
open import Data.Sum.Base
  

private
  infixl 4 _⊡_
  _⊡_ = trans

opaque
  ∘-suc-lemma₁ : ∀ {a b : ℕ} → Nat.suc (a * b + a + b) ≡ suc (b + a * suc b)
  ∘-suc-lemma₁ {a} {b} = cong suc (solve 2 (λ :a :b → :a :* :b :+ :a :+ :b := :b :+ (:a :* (con 1 :+ :b))) refl a b)

  ∘-suc-lemma₂ : ∀ (a b : ℕ) → b * a + b + a ≡ a * b + a + b
  ∘-suc-lemma₂ = solve 2 (λ :a :b → :b :* :a :+ :b :+ :a := :a :* :b :+ :a :+ :b) refl

pair-to : ∀ {a : ℕ} {b : ℕ} → Fin (suc (a * b + a + b)) → Fin (suc a) × Fin (suc b) 
pair-to {a} {b} = 
        remQuot {suc a} (suc b) 
      ∘ cast (∘-suc-lemma₁ {a} {b})

pair-from : ∀ {a : ℕ} {b : ℕ} → Fin (suc a) × Fin (suc b) → Fin (suc (a * b + a + b))
pair-from {a} {b} (fst , snd) = 
        cast (sym (∘-suc-lemma₁ {a} {b}))
        (combine fst snd)
    
-- Taken from the master branch of std library - not in my version
cast-involutive : ∀ {m n} → .(eq₁ : m ≡ n) .(eq₂ : n ≡ m) →
                  ∀ k → cast eq₁ (cast eq₂ k) ≡ k
cast-involutive eq₁ eq₂ k = trans (cast-trans eq₂ eq₁ k) (cast-is-id refl k)

from-to : ∀ {a b : ℕ} {x : Fin (suc (a * b + a + b))} → pair-from {a} {b} (pair-to x) ≡ x
from-to {a} {b} {x} = 
    cong (cast (sym (∘-suc-lemma₁ {a} {b}))) (combine-remQuot (suc b) (cast (∘-suc-lemma₁ {a} {b}) x))
  ⊡ cast-involutive (sym (∘-suc-lemma₁ {a} {b})) (∘-suc-lemma₁ {a} {b}) x

to-from : ∀ {a b : ℕ} {x : Fin (suc a) × Fin (suc b)} → pair-to {a} {b} (pair-from x) ≡ x
to-from {a} {b} {x₁ , x₂} rewrite 
    cast-involutive (∘-suc-lemma₁ {a} {b}) (sym (∘-suc-lemma₁ {a} {b})) (combine x₁ x₂) 
  = remQuot-combine x₁ x₂

ℕ-Mon : Mon
ℕ-Mon = record {
    U    = ℕ
  ; El   = Fin ∘ suc
  ; ε    = 0
  ; _●_ = λ a b → (a * b) + a + b
  ; unit-law  = 1↔⊤
  ; pair-law  = λ a b → record 
                { to        = pair-to
                ; from      = pair-from
                ; to-cong   = λ{refl → refl}
                ; from-cong = λ{refl → refl}
                ; inverse   = (λ{refl → to-from}) , λ{refl → from-to}
                }
  ; comm = λ {u₁} {u₂} → ∘-suc-lemma₂ u₂ u₁
  }

