open import Matrix.Mon
open import ComplexNew
open import Matrix.Leveled.Change-Major

module FFT.Leveled.Specification (cplx : Cplx) (M : Mon) (cm : Change-Major M) where

open Change-Major cm
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

record FFT-Specification : Set where
  field
    --dft : ∀ {n : U} → Ar ((ν n)) ℂ → Ar ((ν n)) ℂ
    dft : ∀ {s : S zz} → Ar s ℂ → Ar s ℂ
    dft-cong : ∀ {s : S zz} 
             → ∀ (xs ys : Ar s ℂ)
             → (prf : ∀ i → xs i ≡ ys i)
             → ∀ i → dft xs i ≡ dft ys i
  
    twiddles : ∀ {l : L} → ∀ {s p : S (ss l)} → P s → P p → ℂ
    
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
            → dft {flatten-z s} (reshape flatten-zᵣ xs) (i ⟨ rev flatten-zᵣ ⟩)
            ≡ reshape CMᵗ (fft {zz} dft twiddles {s} xs) i
            --≡ reshape change-majorᵣ (fft {zz} (λ{ {ν a} → dft}) twiddles {s} xs) i


