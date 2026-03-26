open import Matrix.Mon
open import ComplexNew

module FFT.Leveled.FFT (cplx : Cplx) (M : Mon) where
  open Mon M
  open Cplx cplx

  open import Matrix.Leveled M

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

  fft : (dft : {s : S l} → Ar s ℂ → Ar s ℂ)
       → (twid : ∀ {s p : S (ss l)} → P s → P p → ℂ)
       → {s : S (ss l)} → Ar s ℂ → Ar (transp s) ℂ
  fft dft twid {ι s} a = reshape (up eq) (dft (reshape (down eq) a))
  fft dft twid {s ⊗ p} a = 
    let 
      b = map (fft dft twid) (nest (reshape swap a))
      c = unnest (λ i → zipWith _*_ (twid i) (b i)) 
      d = map (fft dft twid) (nest (reshape swap c))
    in reshape swap (unnest d)

  cmfft : (dft : {s : S l} → Ar s ℂ → Ar s ℂ)
        → (twid : ∀ {s p : S (ss l)} → P s → P p → ℂ)
        → (CM : ∀ {s p : S (ss l)} → Reshape (s ⊗ p) (p ⊗ s))
        → {s : S (ss l)} → Ar s ℂ → Ar s ℂ
  cmfft dft twid CM {ι s} a = reshape (up eq) (dft (reshape (down eq) a))
  cmfft dft twid CM {s ⊗ p} a = 
    let 
      b = map (cmfft dft twid CM) (nest (reshape swap a))
      c = unnest (λ i → zipWith _*_ (twid i) (b i)) 
      d = map (cmfft dft twid CM) (nest (reshape swap c))
    in reshape (CM ∙ swap) (unnest d)

  postulate 
    cmfft-cong : {dft : ∀ {s : S l} → Ar s ℂ → Ar s ℂ}
                {twid : ∀ {s p : S (ss l)} → P s → P p → ℂ}
              → (CM : ∀ {s p : S (ss l)} → Reshape (s ⊗ p) (p ⊗ s))
              → (dft-cong : ∀ {s} a b → (∀ i → a i ≡ b i) 
                          → ∀ i → dft {s} a i ≡ dft b i)
              → ∀ {s : S (ss l)} (a b : Ar s ℂ) → (∀ i → a i ≡ b i)
              → ∀ i → cmfft dft twid CM a i ≡ cmfft dft twid CM b i
              {-
  cmfft-cong {l} {dft} {twid} CM dft-cong {ι s} a b a≡b i = dft-cong (reshape (down eq) a) (reshape (down eq) b) (a≡b ∘ _⟨ down eq ⟩) (i ⟨ up eq ⟩)
  cmfft-cong {l} {dft} {twid} CM dft-cong {s ⊗ p} a b a≡b (i ⊗ j) = ?
  -}
  
  fft-cong : {dft : ∀ {s : S l} → Ar s ℂ → Ar s ℂ}
              {twid : ∀ {s p : S (ss l)} → P s → P p → ℂ}
            → (dft-cong : ∀ {s} a b → (∀ i → a i ≡ b i) 
                        → ∀ i → dft {s} a i ≡ dft b i)
            → ∀ {s : S (ss l)} (a b : Ar s ℂ) → (∀ i → a i ≡ b i)
            → ∀ i → fft dft twid a i ≡ fft dft twid b i
  fft-cong {l} {dft} {twid} dft-cong {ι s} a b a≡b i = dft-cong (reshape (down eq) a) (reshape (down eq) b) (a≡b ∘ _⟨ down eq ⟩) (i ⟨ up eq ⟩)
  fft-cong {l} {dft} {twid} dft-cong {s ⊗ p} a b a≡b (i ⊗ j) = 
    fft-cong dft-cong _ _ 
      (λ k₁ → 
        cong (_ *_) (fft-cong dft-cong _ _ (λ k₂ → a≡b ((k₁ P.⊗ k₂) ⟨ swap ⟩)) j)
      ) 
      i

  fft-dft-cong : ∀ (dft₁ dft₂ : ∀ {s : S l} → Ar s ℂ → Ar s ℂ)
               → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
               → (dft₂-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                            → ∀ i → dft₂ {n} a i ≡ dft₂ b i)
               → (prf : ∀ {s : S l} → ∀ (ys : Ar s ℂ) → ∀ j → dft₁ ys j ≡ dft₂ ys j)
               → ∀ {s : S (ss l)}
               → ∀ (xs : Ar s ℂ)
               → ∀ i
               → fft dft₁ twid xs i ≡ fft dft₂ twid xs i
  fft-dft-cong dft₁ dft₂ dft₂-cong prf {ι s} xs i = prf (reshape (down eq) xs) (i ⟨ up eq ⟩)
  fft-dft-cong dft₁ dft₂ dft₂-cong prf {s₁ ⊗ s₂} xs (i₁ ⊗ i₂) =
      fft-dft-cong _ _ dft₂-cong prf _ i₁
    ⊡ fft-cong dft₂-cong _ _ (λ j → cong (_ *_) (fft-dft-cong _ _ dft₂-cong prf _ i₂)) i₁
