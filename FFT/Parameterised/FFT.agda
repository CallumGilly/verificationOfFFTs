{-# OPTIONS --allow-unsolved-metas #-}
open import Complex using (Cplx)
open import Matrix.Parameterised.Mon


module FFT.Parameterised.FFT (cplx : Cplx) (M : Mon) where

open Cplx cplx using (ℂ) renaming (_*_ to _*ᶜ_)

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Fin as Fin hiding (raise)
open import Data.Bool
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning
--open Eq.Properties
open import Function
open import Algebra.Definitions

open import Data.Unit
-- This gives a warn on older versions of Agda when Product doesnt have a zipWith method
open import Data.Product hiding (swap; map; map₁; map₂; zipWith)
open import Data.Product.Properties
open import Data.Sum as Sum hiding (swap; map)

--postulate
--  ℂ : Set
--  _*ᶜ_ : ℂ → ℂ → ℂ

private
  infixl 4 _⊡_
  _⊡_ = trans


open import Matrix.Parameterised M
open import Matrix.Parameterised.Levels
open Mon M using (U; El)
--open A M
open PL M

private
  variable
    s p : S
    n : U

-- This is the form I really WANT F to take, as opposed to (Ar (ι n) ℂ)
vfft : (dft : ∀ {n : U} → (El n → ℂ) → (El n → ℂ))
     → (twid : ∀ {s p} → P s → P p → ℂ)
     → Ar s ℂ → Ar (transp s) ℂ
vfft {ι x} dft twid = raise-Ar ∘ dft ∘ lower-Ar
vfft {s ⊗ p} dft twid a =
  let 
    b = map (vfft dft twid) (nest (reshape swap a))
    c = unnest (λ i → zipWith _*ᶜ_ (twid i) (b i)) 
    d = map (vfft dft twid) (nest (reshape swap c))
  in reshape swap (unnest d)


vpost-ufft : (dft : ∀ {n : U} → (El n → ℂ) → (El n → ℂ))
       (twid : ∀ {s p} → P s → P p → ℂ)
     → Ar s ℂ → Ar s ℂ
vpost-ufft {ι n} dft twid = raise-Ar ∘ dft ∘ lower-Ar
vpost-ufft {s ⊗ p} dft twid a =
  let 
    c = unnest $ imap 
        (λ i → zipWith _*ᶜ_ (twid {p} {s} i) ∘ vpost-ufft {s} dft twid) 
      (nest (reshape swap a))
    d = map (vpost-ufft {p} dft twid) (nest (reshape swap c))
  in (unnest d)

vpre-ufft : (dft : ∀ {n : U} → (El n → ℂ) → (El n → ℂ))
       (twid : ∀ {s p} → P s → P p → ℂ)
     → Ar s ℂ → Ar s ℂ
vpre-ufft {ι n} dft twid = raise-Ar ∘ dft ∘ lower-Ar
vpre-ufft {s ⊗ p} dft twid a =
  let 
    c = unnest $ imap 
        (λ i → zipWith _*ᶜ_ (twid {s} {p} i) ∘ vpre-ufft {p} dft twid) 
      (nest a)
    d = map (vpre-ufft {s} dft twid) (nest (reshape swap c))
  in reshape swap (unnest d)
-- Parametrised ffts

vfft-dft-cong : ∀ (dft₁ dft₂ : ∀ {n : U} → (El n → ℂ) → (El n → ℂ))
             → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
             → ∀ {s : S}
             → ∀ (xs : Ar s ℂ)
             → (prf : ∀ {n} → ∀ (ys : (El n → ℂ)) → ∀ j → dft₁ ys j ≡ dft₂ ys j)
             → ∀ i
             → vfft dft₁ twid xs i ≡ vfft dft₂ twid xs i
vfft-dft-cong = ?
             
vpost-ufft≡vfft :   ∀ {dft : ∀ {n : U} → (El n → ℂ) → (El n → ℂ)}
           → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
           → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                       → ∀ i → dft {n} a i ≡ dft b i)
           → ∀ (xs : Ar s ℂ)
           → ∀ (i : P s) 
           →  vpost-ufft dft (λ i j → twid i (j ⟨ transpᵣ ⟩)) xs i
              ≡ 
              reshape transpᵣ (vfft  dft twid xs) i --((_⟨_⟩ M i (transpᵣ M)))
vpost-ufft≡vfft = ?
