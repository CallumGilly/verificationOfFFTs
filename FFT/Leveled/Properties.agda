open import Matrix.Mon
open import Complex
open import Matrix.Leveled.Change-Major
open import FFT.Leveled.Specification

module FFT.Leveled.Properties (cplx : Cplx) (M : Mon) (cm : CM M) (spec : FFT-Specification cplx M cm) where

open CM cm
open FFT-Specification spec
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning

open Cplx cplx

open Mon M
open import Matrix.Leveled M

open import FFT.Leveled.FFT cplx M
open import FFT.Leveled.UFFT cplx M

private 
  variable 
    l : L

-- Kind of a basic sanity check before moving onto bigger
dft≡post-ufft : ∀ {s : S l}
         → ∀ (xs : Ar s ℂ)
         → ∀ i
         → reshape (rev (u-flattenᵣ {_} {s})) (dft (reshape u-flattenᵣ xs)) i 
         ≡ reshape (change-majorᵣ ∙ (rev transpᵣ)) (post-ufft dft (λ j₁ j₂ → twiddles j₁ (j₂ ⟨ transpᵣ ⟩)) xs) ?
