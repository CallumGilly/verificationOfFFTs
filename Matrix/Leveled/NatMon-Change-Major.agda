module Matrix.Leveled.NatMon-Change-Major where
open import Matrix.NatMon
open import Matrix.Leveled.Base ℕ-Mon
open import Matrix.Leveled.Reshape ℕ-Mon
open import Matrix.Leveled.Change-Major ℕ-Mon

open import Data.Nat
open import Relation.Binary.PropositionalEquality

ℕ-CM : Change-Major
Change-Major.BaseCM ℕ-CM {s} {p} = subst 
                                      (λ x → Reshape 
                                              (ν x) 
                                              (ν ((u-flatten-z (flatten-z p)) * (u-flatten-z (flatten-z s)) + (u-flatten-z (flatten-z p)) + (u-flatten-z (flatten-z s))))
                                      )
                                      (∘-suc-lemma₂ (u-flatten-z (flatten-z s)) (u-flatten-z (flatten-z p))) 
                                      eq 
