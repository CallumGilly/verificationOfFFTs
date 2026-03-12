{-# OPTIONS --allow-unsolved-metas #-}
open import Complex using (Cplx)
open import Matrix.Mon


module FFT.Parameterised.UFFT (cplx : Cplx) (M : Mon) where

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
open import FFT.Parameterised.FFT cplx M
open Mon M using (U; El)
--open A M
open PL M

private
  variable
    s p : S
    n : U

post-ufft : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
       (twid : ∀ {s p} → P s → P p → ℂ)
     → Ar s ℂ → Ar s ℂ
post-ufft {ι n} dft twid = dft
post-ufft {s ⊗ p} dft twid a =
  let 
    c = unnest $ imap 
        (λ i → zipWith _*ᶜ_ (twid {p} {s} i) ∘ post-ufft {s} dft twid) 
      (nest (reshape swap a))
    d = map (post-ufft {p} dft twid) (nest (reshape swap c))
  in (unnest d)

pre-ufft : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
       (twid : ∀ {s p} → P s → P p → ℂ)
     → Ar s ℂ → Ar s ℂ
pre-ufft {ι n} dft twid = dft
pre-ufft {s ⊗ p} dft twid a =
  let 
    c = unnest $ imap 
        (λ i → zipWith _*ᶜ_ (twid {s} {p} i) ∘ pre-ufft {p} dft twid) 
      (nest a)
    d = map (pre-ufft {s} dft twid) (nest (reshape swap c))
  in reshape swap (unnest d)



post-ufft-cong : {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
            {twid : ∀ {s p} → P s → P p → ℂ}
          → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                      → ∀ i → dft {n} a i ≡ dft b i)
          → ∀ {s} a b → (∀ i → a i ≡ b i)
          → ∀ i → post-ufft {s} dft twid a i ≡ post-ufft dft twid b i
post-ufft-cong dft-cong {ι x} a b a≡b i = dft-cong a b a≡b i
post-ufft-cong dft-cong {s ⊗ p} a b a≡b (i ⊗ j) 
  = post-ufft-cong 
      dft-cong _ _
      (λ k → cong (_ *ᶜ_) 
                  (post-ufft-cong 
                      dft-cong _ _ 
                      (λ l → a≡b (l ⊗ k))
                      i))
      j

pre-ufft-cong : {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
            {twid : ∀ {s p} → P s → P p → ℂ}
          → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                      → ∀ i → dft {n} a i ≡ dft b i)
          → ∀ {s} a b → (∀ i → a i ≡ b i)
          → ∀ i → pre-ufft {s} dft twid a i ≡ pre-ufft dft twid b i
pre-ufft-cong dft-cong a b prf i@(ι _) = dft-cong a b prf i
pre-ufft-cong dft-cong a b prf (i₁ ⊗ i₂) =
  pre-ufft-cong dft-cong _ _ 
    (λ j₁ → 
      cong₂ _*ᶜ_ 
        refl 
        (pre-ufft-cong dft-cong _ _ (λ j₂ → prf (j₁ ⊗ j₂)) i₂)
    ) i₁

post-ufft≡fft :   ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
           → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
           → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                       → ∀ i → dft {n} a i ≡ dft b i)
           → ∀ (xs : Ar s ℂ)
           → ∀ (i : P s) 
           →  post-ufft dft (λ i j → twid i (j ⟨ transpᵣ ⟩)) xs i
              ≡ 
              reshape transpᵣ (fft  dft twid xs) i --((_⟨_⟩ M i (transpᵣ M)))
              --fft  dft twid xs ((_⟨_⟩ M i (transpᵣ M)))
post-ufft≡fft _ _ (ι _) = refl
post-ufft≡fft dft-cong xs (i₁ ⊗ j₁) = 
    (post-ufft-cong dft-cong _ _ (λ i₂ → cong₂ _*ᶜ_ refl (post-ufft≡fft dft-cong _ i₁)) j₁)
    ⊡
    (post-ufft≡fft dft-cong _ j₁)

pre-ufft≡fft′ :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
               → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
               → (transp-twid : ∀ {s p} → ∀ {i j} → twid ((i ⟨ transpᵣ ⟩) ⟨ transpᵣ ⟩) j ≡ twid {s} {p} i j)
               → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                           → ∀ i → dft {n} a i ≡ dft b i)
               → ∀ (xs : Ar s ℂ)
               → ∀ (ys : Ar (transp s) ℂ)
               → (prf : ∀ i → ys (i ⟨ transpᵣ ⟩) ≡ xs i)
               → ∀ (i : P (transp s)) 
               →  (pre-ufft dft (λ i₁ j₁ → twid (i₁ ⟨ transpᵣ ⟩) j₁ ) ys) i
                  ≡ 
                  fft dft twid xs i
pre-ufft≡fft′ {ι x} transp-twid dft-cong xs ys prf = dft-cong ys xs prf
pre-ufft≡fft′ {s₁ ⊗ s₂} {_} {twid} transp-twid dft-cong xs ys prf (i₁ ⊗ i₂) =
    pre-ufft≡fft′ transp-twid dft-cong _ _ 
      (λ j₁ → 
        cong₂ _*ᶜ_ 
          transp-twid
          (pre-ufft≡fft′ transp-twid dft-cong _ _ (λ j₂ → prf (j₂ ⊗ j₁)) i₂)
      )
      i₁

pre-ufft≡fft :   ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
           → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
           → (transp-twid : ∀ {s p} → ∀ {i j} → twid ((i ⟨ transpᵣ ⟩) ⟨ transpᵣ ⟩) j ≡ twid {s} {p} i j)
           → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                       → ∀ i → dft {n} a i ≡ dft b i)
           → ∀ (xs : Ar s ℂ)
           → ∀ (i : P (transp s)) 
           →  (pre-ufft dft (λ i₁ j₁ → twid (i₁ ⟨ transpᵣ ⟩) j₁ ) (reshape (rev transpᵣ) xs)) i
              ≡ 
              (fft  dft twid xs) i
pre-ufft≡fft transp-twid dft-cong xs i = pre-ufft≡fft′ transp-twid dft-cong xs (reshape (rev transpᵣ) xs) (cong xs ∘ rev-eq transpᵣ) i

pre-ufft≡post-ufft :
             ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
           → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
           → (transp-twid : ∀ {s p} → ∀ {i j} → twid ((i ⟨ transpᵣ ⟩) ⟨ transpᵣ ⟩) j ≡ twid {s} {p} i j)
           → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                       → ∀ i → dft {n} a i ≡ dft b i)
           → ∀ (xs : Ar s ℂ)
           → ∀ (i : P (transp s)) 
           → pre-ufft dft (λ j₁ j₂ → twid (j₁ ⟨ transpᵣ ⟩) j₂) (reshape (rev transpᵣ) xs) i
               ≡
             reshape (rev transpᵣ) (post-ufft dft (λ j₁ j₂ → twid j₁ (j₂ ⟨ transpᵣ ⟩)) xs) i
pre-ufft≡post-ufft {s} {dft} {twid} transp-twid dft-cong xs i =
    pre-ufft≡fft {_} {dft} {twid} transp-twid dft-cong xs i
  ⊡ cong (fft dft twid xs) (sym (rev-eq′ transpᵣ i))
  ⊡ sym (post-ufft≡fft {_} {dft} {twid} dft-cong xs (i ⟨ rev transpᵣ ⟩))

