open import Matrix.Mon
open import ComplexNew
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
open import Matrix.Leveled.Base M
open import Matrix.Leveled.Reshape M

open import FFT.Leveled.FFT cplx M
open import FFT.Leveled.UFFT cplx M

open import Function 

private 
  infixl 4 _⊡_
  _⊡_ = trans
  variable 
    l : L

--dft-cong : ∀ {n : U} 
--         → ∀ (xs ys : Ar (ν n) ℂ)
--         → (prf : ∀ i → xs i ≡ ys i)
--         → ∀ i → dft xs i ≡ dft ys i
dft-ι-cong : ∀ {s : S l}
           → ∀ (xs ys : Ar (ι s) ℂ)
           → (prf : ∀ i → xs i ≡ ys i)
           → ∀ (i : P s)
           → ? --(reshape (rev u-flattenᵣ) ∘ dft ∘ reshape  u-flattenᵣ) xs i
--           ≡ (reshape (rev u-flattenᵣ) ∘ dft ∘ reshape  u-flattenᵣ) ys i
--dft-ι-cong {.L.zz} {ν x} xs ys prf i@(ν _) = dft-cong _ _ prf i
--dft-ι-cong {.(L.ss _)} {ι s} xs ys prf i = dft-cong _ _ (λ j → prf (j ⟨ u-flattenᵣ ⟩)) (i ⟨ rev u-flattenᵣ ⟩)
--dft-ι-cong {l}     {s₁ ⊗ s₂} xs ys prf i = dft-cong _ _ (λ j → prf (j ⟨ u-flattenᵣ ⟩)) (i ⟨ rev u-flattenᵣ ⟩)
  

fft₁≡fft₂ : ∀ {s : S (ss (ss l))}
          → (dft : {s : S (ss l)} → Ar (ι s) ℂ → Ar (ι s) ℂ)
          → (twid : ∀ {s p : S (ss (ss l))} → P s → P p → ℂ)
          → ∀ (xs : Ar s ℂ)
          → ∀ (i : P s)
          → fft 
              {l} 
              (λ ys → reshape (down eq) (dft (reshape (up eq) ys))) 
              (λ j₁ j₂ → twid (j₁ ⟨ down eq ⟩) (j₂ ⟨ down eq ⟩)) 
              {flatten s} 
              (reshape flattenᵣ xs)
              (i ⟨ (rev flattenᵣ) ∙ change-majorᵣ ⟩)
          ≡ fft 
              {ss l} 
              dft 
              twid 
              {s} 
              xs 
              (i ⟨ change-majorᵣ ⟩)
fft₁≡fft₂ {l} {s} dft₁ twid xs i = ?

{-
lemma₁ : ∀ (s : S (ss l)) → u-flatten s ≡ u-flatten (flatten s)
lemma₁ (ι s) = refl
lemma₁ (s₁ ⊗ s₂) rewrite
    lemma₁ s₁
  | lemma₁ s₂ 
  = refl


foo : ∀ {l}{s : S (ss l)} → Reshape (ν (u-flatten (flatten s))) (ν (u-flatten s))
foo {s = ι s} = eq
foo {s = s ⊗ p} = (flat ∙ (foo {_} {s} ⊕ foo {_} {p}) ) ∙ unflat

tmp₁ : ∀ {s : S (ss l)} 
     → ∀ (i : P s) 
     → i ⟨ rev (u-flattenᵣ ∙ flattenᵣ) ⟩ 
     ≡ i ⟨ (rev u-flattenᵣ) ∙ ? ⟩ 
-}

{-
Peq : ∀ {s₁ s₂ : S l} 
               → ∀ (prf  : s₁ ≡ s₂) 
               → P s₁ → P s₂
Peq refl x = x

tmp₁ : ∀ {s : S (ss l)} 
     → ∀ (i : P s) 
     → i ⟨ rev (u-flattenᵣ ∙ flattenᵣ) ⟩ 
     ≡ i ⟨ (rev u-flattenᵣ) ∙ subst (λ t → Reshape ? ?) (cong ν (lemma₁ s)) eq ⟩
     --≡ Peq (cong ν (lemma₁ s)) (i ⟨ rev u-flattenᵣ ⟩)
tmp₁ {l} {ι s} (ι i) = refl
tmp₁ {zz} {s₁ ⊗ s₂} (i₁ ⊗ i₂) = ?
tmp₁ {ss l} {s₁ ⊗ s₂} (i₁ ⊗ i₂) = ?

-}

{-
betterEquality : ∀ {s₁ s₂ : S l} 
               → ∀ (prf  : s₁ ≡ s₂) 
               → ∀ {X : Set}
               → ∀ (xs : Ar s₁ X) (ys : Ar s₂ X) 
               → (prf₂ : ∀ (i : P s₁) → xs i ≡ ys (i ⟨ subst (λ t → Reshape t s₁) prf eq ⟩))
               → ?
               --→ ∀ i → xs i ≡ ys i
-}

prfu : ∀ {l : L} → ∀ {s : S (ss l)} → ∀ (i : P s) → i ⟨ rev u-flattenᵣ ⟩ ≡ ?
dft-lcong : ∀ {u₁ u₂ : U} 
          → ∀ {X : Set}
          → (u₁ ≡ u₂) 
          → (xs : Ar (ι (ν u₁)) X) 
          → (ys : Ar (ι (ν u₂)) X) 
          → ?


dftl : {l : L} {s : S (ss (ss l))} {xs : Ar s ℂ} {i : P s} →
       dft (reshape u-flattenᵣ xs) (i ⟨ rev u-flattenᵣ ⟩) ≡
       dft (reshape u-flattenᵣ (reshape flattenᵣ xs))
       ((i ⟨ rev flattenᵣ ⟩) ⟨ rev u-flattenᵣ ⟩)
dftl {l} {ι s} {xs} {ι i} = refl
dftl {l} {s₁ ⊗ s₂} {xs} {i₁ ⊗ i₂} = ?

gen-dft≡fft : ∀ {s : S (ss l)}
            → ∀ (xs : Ar s ℂ)
            → ∀ (i : P s)
            → dft {u-flatten s} (reshape u-flattenᵣ xs) (i ⟨ rev u-flattenᵣ ⟩)
            ≡ reshape change-majorᵣ (fft {l} (reshape (rev u-flattenᵣ) ∘ dft ∘ reshape u-flattenᵣ) twiddles {s} xs) i
gen-dft≡fft {zz} {s} xs i = 
    dft≡fft xs i
  ⊡ ?
gen-dft≡fft {ss l} {s} xs i =
    dftl {l} {s} {xs} {i}
  ⊡ 
    gen-dft≡fft {l} {flatten s} (reshape flattenᵣ xs) (i ⟨ rev flattenᵣ ⟩)
  ⊡
    ? --gen-dft≡fft {l} {flatten s} ? ?


-- Kind of a basic sanity check before moving onto bigger
    -- Which has been useful - because I currently can only make proofs upon one level
    -- and proof against the DFT for (xs ∈ ss zz)..
dft≡post-ufft : ∀ {s : S (ss l)}
         → ∀ (xs : Ar s ℂ)
         → ∀ i
         → (reshape (rev u-flattenᵣ) ∘ dft ∘ reshape  u-flattenᵣ) xs i 
         ≡ reshape 
              (change-majorᵣ ∙ (rev transpᵣ)) 
              (post-ufft (reshape (rev u-flattenᵣ) ∘ dft ∘ reshape  u-flattenᵣ) (λ j₁ j₂ → twiddles j₁ (j₂ ⟨ transpᵣ ⟩)) xs) 
              i
dft≡post-ufft {l} {s} xs i = 
    gen-dft≡fft xs i
  ⊡ 
    cong 
        (fft (λ x i₁ → dft (λ i₂ → x (i₂ ⟨ u-flattenᵣ ⟩)) (i₁ ⟨ rev u-flattenᵣ ⟩)) twiddles xs)
        (sym (rev-eq′ transpᵣ (i ⟨ CM.change-majorᵣ cm ⟩)))
  ⊡ 
    ? --sym (post-ufft≡fft {l} {reshape (rev u-flattenᵣ) ∘ dft ∘ reshape  u-flattenᵣ} {twiddles} dft-ι-cong {s} xs ((i ⟨ CM.change-majorᵣ cm ⟩) ⟨ rev transpᵣ ⟩))

-- This is how I really want to be defining the FFT which is equal to the DFT
-- But I need the DFT to be defined not on ν to allow for fft to take its 
-- place
{-
fftν : (dft : ∀ {u : U} → Ar (ν u) ℂ → Ar (ν u) ℂ)
    → (twid : ∀ {s p : S (zz)} → P s → P p → ℂ)
    → ∀ {s : S zz} → Ar s ℂ → Ar (transp s) ℂ
fftν dft twid {ν x} xs i@(ν _) = (dft xs) i
fftν dft twid {s₁ ⊗ s₂} a (i₁ ⊗ i₂) =
  let 
    b = map (fftν dft twid) (nest (reshape swap a))
    c = unnest (λ i → zipWith _*_ (twid i) (b i))
    d = map (fftν dft twid) (nest (reshape swap c))
  in reshape swap (unnest d) (i₁ ⊗ i₂)

fftν≡fft : ∀ (dft : ∀ {u : U} → Ar (ν u) ℂ → Ar (ν u) ℂ) 
        → ∀ {twid : ∀ {s p : S (ss zz)} → P s → P p → ℂ}
        → ∀ {s : S zz}
        → ∀ (xs : Ar s ℂ)
        → fftν dft (λ j₁ j₂ → twid (j₁ ⟨ down eq ⟩) (j₂ ⟨ down eq ⟩)) xs ?
        ≡ fft {zz} (reshape (rev u-flattenᵣ) ∘ dft ∘ reshape u-flattenᵣ) twid {ι s} (reshape (up eq) xs) ?
-}
