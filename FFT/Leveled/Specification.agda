open import Matrix.Mon
open import Complex
open import Matrix.Leveled.Change-Major

module FFT.Leveled.Specification (cplx : Cplx) (M : Mon) (cm : CM M) where

open CM cm
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

record FFT-Specification : Set where
  field
    dft : ∀ {n : U} → Ar (ν n) ℂ → Ar (ν n) ℂ
    dft-cong : ∀ {n : U} 
             → ∀ (xs ys : Ar (ν n) ℂ)
             → (prf : ∀ i → xs i ≡ ys i)
             → ∀ i → dft xs i ≡ dft ys i
  
    twiddles : ∀ {s p : S l} → P s → P p → ℂ
    
    dft≡fft : ∀ {s : (?)}
        → ∀ (xs : Ar (ν s) ℂ)
        → ∀ i
        → reshape (rev u-flattenᵣ) (dft (reshape (u-flattenᵣ) xs)) i
        ≡ reshape change-majorᵣ (fft {?} dft twiddles {s} xs) i

