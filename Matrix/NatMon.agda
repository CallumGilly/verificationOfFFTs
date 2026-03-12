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
import Matrix.Simple.Base as M
import Matrix.Simple.Equality as ME
open import Matrix.Simple.NonZero
import Data.Fin as Fin
open import Data.Fin.Properties
open import Function.Bundles
open Inverse
open import Matrix.Parameterised.Base
open import Data.Nat.Solver
open +-*-Solver
open import Data.Sum.Base
  

private
  infixl 4 _⊡_
  _⊡_ = trans

opaque
  lemma : ∀ {a b : ℕ} → Nat.suc (a * b + a + b) ≡ suc (b + a * suc b)
  lemma {a} {b} = cong suc (solve 2 (λ :a :b → :a :* :b :+ :a :+ :b := :b :+ (:a :* (con 1 :+ :b))) refl a b)

pair-to : ∀ {a : ℕ} {b : ℕ} → Fin (suc (a * b + a + b)) → Fin (suc a) × Fin (suc b) 
pair-to {a} {b} = 
        remQuot {suc a} (suc b) 
      ∘ cast (lemma {a} {b})

pair-from : ∀ {a : ℕ} {b : ℕ} → Fin (suc a) × Fin (suc b) → Fin (suc (a * b + a + b))
pair-from {a} {b} (fst , snd) = 
        cast (sym (lemma {a} {b}))
        (combine fst snd)

from-to : ∀ {a b : ℕ} {x : Fin (suc (a * b + a + b))} → pair-from {a} {b} (pair-to x) ≡ x
from-to {a} {b} {x} = 
    sym (subst-is-cast (sym $ lemma {a} {b}) ?)
  ⊡
    ?
--asd : ∀ {a} {b} {fst = x₁ : Fin (suc a)} {snd = x₂ : Fin (suc b)} →
--      quotRem (suc b) (cast _ (pair-from (x₁ , x₂))) .proj₂ ≡
--      quotRem (suc b) (combine x₁ x₂) .proj₂
asdfafds : ∀ {a} {b} {fst = x₁ : Fin (suc a)}
             {snd = x₂ : Fin (suc b)} →
           proj₂ (quotRem (suc b) (cast _ (pair-from (x₁ , x₂)))) ≡
           proj₂ (quotRem (suc b) (combine x₁ x₂))
asdfafds {a} {b} {fst = x₁} {snd = x₂} = ?
to-from : ∀ {a b : ℕ} {x : Fin (suc a) × Fin (suc b)} → pair-to {a} {b} (pair-from x) ≡ x
to-from {a} {b} {x₁ , x₂} =
      cong₂ _,_ (cong proj₂ (cong₂ _,_ refl ?)) (?)
    ⊡ 
      remQuot-combine x₁ x₂

ℕ-Mon : Mon
ℕ-Mon = record {
    U    = ℕ
  ; El   = Fin ∘ suc
  ; ε    = 0
  --; _●_  = λ a b → (Nat.pred a) * (Nat.pred b)
  --; _●_  = λ a b → ((a * b) ∸ a) ∸ b
  ; _●_ = λ a b → (a * b) + a + b
  ; unit-law  = 1↔⊤
  ; pair-law  = λ a b → record 
                { to        = pair-to
                ; from      = pair-from
                ; to-cong   = λ{refl → refl}
                ; from-cong = λ{refl → refl}
                ; inverse   = ? , λ{refl → ?}
                }
  ; comm = λ {u₁} {u₂} → solve 2 (λ :a :b → :a :* :b :+ :a :+ :b := :b :* :a :+ :b :+ :a) refl u₁ u₂
  }

open import Matrix.Leveled.Change-Major ℕ-Mon
Leveled-CM : CM
Leveled-CM = ?
