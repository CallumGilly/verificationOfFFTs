{-# OPTIONS --allow-unsolved-metas #-}
module Matrix.Leveled.NatMon-Change-Major where
open import Matrix.NatMon
open import Matrix.Leveled.Base ℕ-Mon
open import Matrix.Leveled.Reshape ℕ-Mon
open import Matrix.Leveled.Change-Major ℕ-Mon

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

ℕ-CM : Change-Major
Change-Major.BaseCM ℕ-CM {s} {p} = subst (λ x → Reshape (ν x) (ν (p * s + p + s))) (∘-suc-lemma₂ s p) eq
Change-Major.CM-preserves-order ℕ-CM {n} {m} (ν x) =
  begin
    iota′ (ν x ⟨ subst (λ x₁ → Reshape (ν x₁) (ν (n * m + n + m))) (∘-suc-lemma₂ m n) eq ⟩)
  ≡⟨⟩
    iota′ (_⟨_⟩ (ν x) (subst (λ x₁ → Reshape (ν x₁) (ν (n * m + n + m))) (∘-suc-lemma₂ m n) eq))
  ≡⟨ subst-application (λ a → ?) ? (∘-suc-lemma₂ m n) ⟩
    ? --iota′ (_⟨_⟩ (ν x) (subst (λ x₁ → Reshape (ν x₁) (ν (n * m + n + m))) (∘-suc-lemma₂ m n) eq))
  ≡⟨ ? ⟩
    iota′ (ν x)
  ∎

