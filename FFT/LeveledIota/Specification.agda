open import Matrix.Mon
open import ComplexNew
open import Matrix.Leveled.Change-Major

module FFT.Leveled.Specification (cplx : Cplx) (M : Mon) (cm : CM M) where

open CM cm
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning
open import Function

open Cplx cplx

open Mon M
open import Matrix.Leveled M

open import FFT.Leveled.FFT cplx M
--open import FFT.Leveled.UFFT cplx M

private 
  variable 
    l : L

dft-wrapper : 
    ∀ (dft : ∀ {n : U} → Ar (ι (ν n)) ℂ → Ar (ι (ν n)) ℂ)
    → (∀ {s : S zz} → Ar (ι s) ℂ → Ar (ι s) ℂ)
dft-wrapper dft {ν _} = dft

record FFT-Specification : Set where
  field
    dft : ∀ {n : U} → Ar (ι (ν n)) ℂ → Ar (ι (ν n)) ℂ
    dft-cong : ∀ {n : U} 
             → ∀ (xs ys : Ar (ι (ν n)) ℂ)
             → (prf : ∀ i → xs i ≡ ys i)
             → ∀ i → dft xs i ≡ dft ys i
  
    twiddles : ∀ {s p : S (ss l)} → P s → P p → ℂ
    
    {-
    I really like this relation, but I think it is too high level and would 
    thus require more "unparamaterised" work than really needed. Hopefully I 
    can spec a smaller proof and generate the below... -} {-
    dft≡fft : ∀ {s : S (ss l)}
        → ∀ (xs : Ar s ℂ)
        → ∀ i
        → reshape (rev u-flattenᵣ) (dft (reshape (u-flattenᵣ) xs)) i
        ≡ reshape change-majorᵣ (fft {l} (reshape (rev u-flattenᵣ) ∘ dft ∘ reshape u-flattenᵣ) twiddles {s} xs) i
    -}

    dft≡fft : ∀ {s : S (ss zz)}
            → ∀ (xs : Ar s ℂ)
            → ∀ (i : P s)
            → dft (reshape u-flattenᵣ xs) (i ⟨ rev u-flattenᵣ ⟩)
            ≡ reshape change-majorᵣ (fft {zz} (dft-wrapper dft) twiddles {s} xs) i
            --≡ reshape change-majorᵣ (fft {zz} (λ{ {ν a} → dft}) twiddles {s} xs) i


