open import Matrix.Mon
open import ComplexNew

module FFT.Leveled.UFFT (cplx : Cplx) (M : Mon) where

open Mon M
open Cplx cplx

open import Matrix.Leveled M
open import FFT.Leveled.FFT cplx M

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning

open import Function
open import Algebra.Definitions

private
  infixl 4 _⊡_
  _⊡_ = trans

  variable
    l : L

post-ufft : (dft : ∀ {s : S l} → Ar (ι s) ℂ → Ar (ι s) ℂ)
          → (twid : ∀ {s p : S (ss l)} → P s → P p → ℂ)
          → ∀ {s : S (ss l)}
          → Ar s ℂ → Ar s ℂ
post-ufft dft twid {ι n} = dft 
post-ufft dft twid {s ⊗ p} a =
  let 
    c = unnest $ imap 
        (λ i → zipWith _*_ (twid {p} {s} i) ∘ post-ufft dft twid {s}) 
      (nest (reshape swap a))
    d = map (post-ufft dft twid {p}) (nest (reshape swap c))
  in (unnest d)

pre-ufft : (dft : ∀ {s : S l} → Ar (ι s) ℂ → Ar (ι s) ℂ)
         → (twid : ∀ {s p : S (ss l)} → P s → P p → ℂ)
         → ∀ {s : S (ss l)}
         → Ar s ℂ → Ar s ℂ
pre-ufft dft twid {ι n} = dft
pre-ufft dft twid {s ⊗ p} a =
  let 
    c = unnest $ imap 
        (λ i → zipWith _*_ (twid {s} {p} i) ∘ pre-ufft dft twid {p})
      (nest a)
    d = map (pre-ufft dft twid {s}) (nest (reshape swap c))
  in reshape swap (unnest d)


post-ufft-cong : {dft : ∀ {s : S l} → Ar (ι s) ℂ → Ar (ι s) ℂ}
            {twid : ∀ {s p : S (ss l)} → P s → P p → ℂ}
          → (dft-cong : ∀ {s} a b → (∀ i → a i ≡ b i) 
                      → ∀ i → dft {s} a i ≡ dft b i)
          → ∀ {s : S (ss l)} a b → (∀ i → a i ≡ b i)
          → ∀ i → post-ufft dft twid {s} a i ≡ post-ufft dft twid b i
post-ufft-cong dft-cong {ι x} = dft-cong 
post-ufft-cong dft-cong {s ⊗ p} a b a≡b (i ⊗ j) 
  = post-ufft-cong 
      dft-cong _ _
      (λ k → cong (_ *_) 
                  (post-ufft-cong 
                      dft-cong _ _ 
                      (λ l → a≡b (l ⊗ k))
                      i))
      j

pre-ufft-cong : {dft : ∀ {s : S l} → Ar (ι s) ℂ → Ar (ι s) ℂ}
            {twid : ∀ {s p : S (ss l)} → P s → P p → ℂ}
          → (dft-cong : ∀ {s} a b → (∀ i → a i ≡ b i) 
                      → ∀ i → dft {s} a i ≡ dft b i)
          → ∀ {s} a b → (∀ i → a i ≡ b i)
          → ∀ i → pre-ufft dft twid {s} a i ≡ pre-ufft dft twid b i
pre-ufft-cong dft-cong a b prf i@(ι _) = dft-cong _ _ prf i
pre-ufft-cong dft-cong a b prf (i₁ ⊗ i₂) =
  pre-ufft-cong dft-cong _ _ 
    (λ j₁ → 
      cong₂ _*_ 
        refl 
        (pre-ufft-cong dft-cong _ _ (λ j₂ → prf (j₁ ⊗ j₂)) i₂)
    ) i₁

post-ufft≡fft :   ∀ {dft : ∀ {s : S l} → Ar (ι s) ℂ → Ar (ι s) ℂ}
           → ∀ {twid : ∀ {s p : S (ss l)} → P s → P p → ℂ}
           → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                       → ∀ i → dft {n} a i ≡ dft b i)
           → ∀ {s : S (ss l)}
           → ∀ (xs : Ar s ℂ)
           → ∀ (i : P s) 
           →  post-ufft dft (λ i j → twid i (j ⟨ transpᵣ ⟩)) xs i
              ≡ 
              reshape transpᵣ (fft  dft twid xs) i
post-ufft≡fft _ _ (ι _) = refl
post-ufft≡fft dft-cong xs (i₁ ⊗ j₁) = 
    (post-ufft-cong dft-cong _ _ (λ i₂ → cong₂ _*_ refl (post-ufft≡fft dft-cong _ i₁)) j₁)
    ⊡
    (post-ufft≡fft dft-cong _ j₁)

pre-ufft≡fft′ :  ∀ {dft : ∀ {s : S l} → Ar (ι s) ℂ → Ar (ι s) ℂ}
               → ∀ {twid : ∀ {s p : S (ss l)} → P s → P p → ℂ}
               → (transp-twid : ∀ {s p} → ∀ {i j} → twid ((i ⟨ transpᵣ ⟩) ⟨ transpᵣ ⟩) j ≡ twid {s} {p} i j)
               → (dft-cong : ∀ {s} a b → (∀ i → a i ≡ b i) 
                           → ∀ i → dft {s} a i ≡ dft b i)
               → ∀ {s : S (ss l)}
               → ∀ (xs : Ar s ℂ)
               → ∀ (ys : Ar (transp s) ℂ)
               → (prf : ∀ i → ys (i ⟨ transpᵣ ⟩) ≡ xs i)
               → ∀ (i : P (transp s)) 
               →  (pre-ufft dft (λ i₁ j₁ → twid (i₁ ⟨ transpᵣ ⟩) j₁ ) ys) i
                  ≡ 
                  fft dft twid xs i
pre-ufft≡fft′ transp-twid dft-cong {ι x} xs ys prf i = dft-cong _ _ prf i
pre-ufft≡fft′ {_} {_} {twid} transp-twid dft-cong {s₁ ⊗ s₂} xs ys prf (i₁ ⊗ i₂) =
    pre-ufft≡fft′ transp-twid dft-cong _ _ 
      (λ j₁ → 
        cong₂ _*_ 
          transp-twid
          (pre-ufft≡fft′ transp-twid dft-cong _ _ (λ j₂ → prf (j₂ ⊗ j₁)) i₂)
      )
      i₁

pre-ufft≡fft :   ∀ {dft : ∀ {s : S l} → Ar (ι s) ℂ → Ar (ι s) ℂ}
           → ∀ {twid : ∀ {s p : S (ss l)} → P s → P p → ℂ}
           → (transp-twid : ∀ {s p} → ∀ {i j} → twid ((i ⟨ transpᵣ ⟩) ⟨ transpᵣ ⟩) j ≡ twid {s} {p} i j)
           → (dft-cong : ∀ {s} a b → (∀ i → a i ≡ b i) 
                       → ∀ i → dft {s} a i ≡ dft b i)
           → ∀ {s : S (ss l)}
           → ∀ (xs : Ar s ℂ)
           → ∀ (i : P (transp s)) 
           →  (pre-ufft dft (λ i₁ j₁ → twid (i₁ ⟨ transpᵣ ⟩) j₁ ) (reshape (rev transpᵣ) xs)) i
              ≡ 
              (fft  dft twid xs) i
pre-ufft≡fft transp-twid dft-cong xs i = pre-ufft≡fft′ transp-twid dft-cong xs (reshape (rev transpᵣ) xs) (cong xs ∘ rev-eq transpᵣ) i

pre-ufft≡post-ufft :
             ∀ {dft : ∀ {s : S l} → Ar (ι s) ℂ → Ar (ι s) ℂ}
           → ∀ {twid : ∀ {s p : S (ss l)} → P s → P p → ℂ}
           → (transp-twid : ∀ {s p} → ∀ {i j} → twid ((i ⟨ transpᵣ ⟩) ⟨ transpᵣ ⟩) j ≡ twid {s} {p} i j)
           → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                       → ∀ i → dft {n} a i ≡ dft b i)
           → ∀ {s : S (ss l)}
           → ∀ (xs : Ar s ℂ)
           → ∀ (i : P (transp s)) 
           → pre-ufft dft (λ j₁ j₂ → twid (j₁ ⟨ transpᵣ ⟩) j₂) (reshape (rev transpᵣ) xs) i
               ≡
             reshape (rev transpᵣ) (post-ufft dft (λ j₁ j₂ → twid j₁ (j₂ ⟨ transpᵣ ⟩)) xs) i
pre-ufft≡post-ufft {s} {dft} {twid} transp-twid dft-cong xs i =
    pre-ufft≡fft {_} {dft} {twid} transp-twid dft-cong xs i
  ⊡ cong (fft dft twid xs) (sym (rev-eq′ transpᵣ i))
  ⊡ sym (post-ufft≡fft {_} {dft} {twid} dft-cong xs (i ⟨ rev transpᵣ ⟩))
