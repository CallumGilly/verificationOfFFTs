{-# OPTIONS --allow-unsolved-metas #-}
open import ComplexNew

module FFT.Leveled.dft (cplx : Cplx) where


open Cplx cplx
open import Matrix.Mon
open import Matrix.NatMon
open import Matrix.Leveled.Base ℕ-Mon
open import Matrix.Leveled.Reshape ℕ-Mon
open import Matrix.Leveled.Change-Major ℕ-Mon
open import Matrix.Leveled.NatMon-Sum cplx
open import Matrix.Leveled.NatMon-Change-Major
open Mon ℕ-Mon
open import FFT.Leveled.Specification cplx ℕ-Mon ℕ-CM
open import FFT.Leveled.FFT cplx ℕ-Mon
open Change-Major ℕ-CM

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning

open import Data.Fin hiding (_+_; pred)
open import Data.Nat renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties

private
  variable
    ℓ : L
    n : U
    X : Set

-- Be careful here, given i : Fin ∘ suc
--iota : ∀ {n : U} → Ar (ι (ν n)) ℕ
--iota (ι (ν x)) = toℕ x

ℕ-twiddles : ∀ {s p : S (ss ℓ)} → ℕ → P s → P p → ℂ
ℕ-twiddles {l} {s} {p} n i j = -ω n ((iota (i ⟨ rev u-flattenᵣ ⟩)) *ₙ (iota (j ⟨ rev u-flattenᵣ ⟩)))


length-transp : ∀ (s : S ℓ) → length s ≡ length (transp s)
length-transp (ν x) = refl
length-transp (ι s) = refl
length-transp (s₁ ⊗ s₂) rewrite length-transp s₁ | length-transp s₂ = ?

module ℕ-dft′ where
  dft : ∀ {s : S zz} 
        → Ar s ℂ 
        → Ar s ℂ
  dft {ν n} xs j = sum (λ k → xs k * ℕ-twiddles n (ι k) (ι j))

  dft-cong : ∀ {s : S zz} (xs ys : Ar s ℂ) →
             ((i : P s) → xs i ≡ ys i) → (i : P s) → dft xs i ≡ dft ys i
  dft-cong {ν n} xs ys prf (ν j) = sum-cong 
                                    {n} 
                                    {(λ k → xs k * -ω n (iota (P.ι k) *ₙ toℕ j))} 
                                    {(λ k → ys k * -ω n (iota (P.ι k) *ₙ toℕ j))} 
                                    λ{ (ν i) → 
                                      cong₂ _*_ (prf (ν i)) refl
                                    } 

  twiddles : ∀ {s p : S (ss ℓ)} → P s → P p → ℂ
  twiddles {_} {s} {p} i j = ℕ-twiddles (length s *ₙ length p) i j

  twiddles-CMᵗᵣ-lemma : ∀ {s p : S (ss ℓ)}
                      → ∀ (i : P s) 
                      → ∀ (j : P p) 
                      → twiddles i (j ⟨ CMᵗ ⟩) ≡ twiddles i j
  twiddles-CMᵗᵣ-lemma {ℓ} {s} {.(S.ι _)} i (ι j) = refl
  twiddles-CMᵗᵣ-lemma {ℓ} {s} {(p₁ ⊗ p₂)} i (j₁ ⊗ j₂) rewrite length-transp p₁ | length-transp p₂ = cong₂ -ω ? ?

  twiddles-flatten-zᵣ-lemma : ∀ {s p : S (ss (ss ℓ))}
                            → ∀ (i : P (flatten-z s))
                            → ∀ (j : P (flatten-z p))
                            → twiddles {_} {s} {p} (i ⟨ flatten-zᵣ ⟩) (j ⟨ flatten-zᵣ ⟩)
                            ≡ twiddles i j

  twiddles-rev-flatten-zᵣ-lemma : {s p
                                 : S (ss (ss ℓ))}
                                (i : P s) (j : P p) →
                                twiddles (i ⟨ rev flatten-zᵣ ⟩) (j ⟨ rev flatten-zᵣ ⟩) ≡
                                twiddles i j
  twiddles-transₗ-lemma : {s p : S (ss ℓ)}
                        (i : P s) (j : P p) →
                        twiddles (i ⟨ transpᵣ ∙ transpᵣ ⟩) j ≡
                        twiddles i j
  dft≡fft : {s : S (ss zz)}
          (xs : Ar s ℂ) (i : P s) →
          dft (reshape flatten-zᵣ xs) (i ⟨ rev flatten-zᵣ ⟩) ≡
          reshape CMᵗ (fft dft twiddles xs) i


ℕ-dft : FFT-Specification
ℕ-dft = record {ℕ-dft′
               ; twiddles-flatten-zᵣ-lemma = λ {l} {s} {p} → ℕ-dft′.twiddles-flatten-zᵣ-lemma {_} {s} {p}
               }



    --record
        -- { -- ℕ-dft′
        -- ; twiddles-CMᵗᵣ-lemma = ?
        -- ; twiddles-flatten-zᵣ-lemma = ?
        -- ; twiddles-rev-flatten-zᵣ-lemma = ?
        -- ; twiddles-transₗ-lemma = ?
        -- ; dft≡fft = ?
        -- }
