open import Matrix.Mon
open import ComplexNew
open import Matrix.Leveled.Change-Major
open import FFT.Leveled.Specification

module FFT.Leveled.Properties (cplx : Cplx) (M : Mon) (change-major : Change-Major M) (spec : FFT-Specification cplx M change-major) where

open Change-Major change-major
open FFT-Specification spec
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂)
open Eq.≡-Reasoning

open Cplx cplx

open Mon M
open import Matrix.Leveled.Base M
open import Matrix.Leveled.Reshape M

open import FFT.Leveled.FFT cplx M
open import FFT.Leveled.UFFT cplx M

open import Function 
open import Data.Product hiding (swap; map)
open import Data.Product.Properties


private 
  infixl 4 _⊡_
  _⊡_ = trans

  variable 
    l : L

CM-flatten-comm : ∀ {s₁ s₂ : S (ss (ss l))}
       → ∀ (i₁ : P s₁)
       → ∀ (i₂ : P s₂)
       →  (i₁ ⊗ i₂) ⟨ CM ∙ rev flatten-zᵣ ⊕ rev flatten-zᵣ ⟩
        ≡
          (i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ⊕ rev flatten-zᵣ ∙ CM ⟩
CM-flatten-comm {l} {s₁} {s₂} i₁ i₂ rewrite rev-eq (_⊕_ {_} {_} {s₂} {s₁} flatten-zᵣ flatten-zᵣ) ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ⊕ rev flatten-zᵣ ∙ CM ⟩)  = refl

cmfft-icong : ∀ {s : S (ss l)}
             → ∀ {dft₁ : {s : S l} → Ar s ℂ → Ar s ℂ}
             → ∀ {twid : ∀ {r : L} → ∀ {s p : S r} → P s → P p → ℂ}
             → ∀ (xs : Ar s ℂ)
             → ∀ (i j : P s)
             → i ≡ j
             → cmfft dft₁ twid CM xs i ≡ cmfft dft₁ twid CM xs j
cmfft-icong _ _ _ refl = refl

⊕-distributes-∙ : ∀ {l₁ l₂ l₃ : L} 
                → ∀ {p₁ p₂ : S (ss l₁)}
                → ∀ {s₁ : S (ss l₂)} → ∀ (r₁ : Reshape s₁ p₁ )
                → ∀ {s₂ : S (ss l₂)} → ∀ (r₂ : Reshape s₂ p₂ )
                → ∀ {p₃ : S (ss l₃)} → ∀ (r₃ : Reshape p₃ s₁ )
                → ∀ {p₄ : S (ss l₃)} → ∀ (r₄ : Reshape p₄ s₂ )
                → ∀ (i : P (p₁ ⊗ p₂))
                → i ⟨ ((r₁ ⊕ r₂) ∙ (r₃ ⊕ r₄)) ⟩ ≡ i ⟨ ((r₁ ∙ r₃) ⊕ (r₂ ∙ r₄)) ⟩
⊕-distributes-∙ r₁ r₂ r₃ r₄ (i₁ ⊗ i₂) = refl

cmfft₂≡cmfft₁ : ∀ {s : S (ss (ss l))}
     → ∀ {dft : {s : S l} → Ar s ℂ → Ar s ℂ}
     → ∀ {twid : ∀ {r : L} → ∀ {s p : S r} → P s → P p → ℂ}
     → ∀ {dft-cong : ∀ {p : S l} → (a b : Ar p ℂ) → (prf : ∀ i → a i ≡ b i) → ∀ i → dft a i ≡ dft b i}
     → ∀ {twid-♭ : ∀ {r : L} → ∀ {s p : S (ss r)} → ∀ (i : P s) (j : P p) → twid i j ≡ twid (i ⟨ rev flatten-zᵣ ⟩) (j ⟨ rev flatten-zᵣ ⟩)}
     → ∀ (xs : Ar s ℂ)
     → ∀ (i : P s)
     → cmfft {ss l} (cmfft dft twid CM) twid CM {s} xs i ≡ cmfft {l} dft twid CM {flatten-z s} (reshape flatten-zᵣ xs) (i ⟨ rev flatten-zᵣ ⟩)
cmfft₂≡cmfft₁ {l} {ι s} {dft₁} {twid} xs (ι i) = refl
cmfft₂≡cmfft₁ {l} {s₁ ⊗ s₂} {dft₁} {twid} {dft₁-cong} {twid-♭} xs i@(i₁ ⊗ i₂) = 
    remQuot-splits-proof 
        {xs = unnest _} 
        {ys = unnest _} 
        (λ j₁ j₂ → 
            cmfft₂≡cmfft₁ {_} {_} {_} {twid} {dft₁-cong} {twid-♭} _ j₂
          ⊡ cmfft-cong CM dft₁-cong _ _ (λ k₁ → 
              cong₂ _*_
                refl
                (cmfft₂≡cmfft₁ {_} {s₁} {_} {twid} {dft₁-cong} {twid-♭} _ j₁)
            ) (j₂ ⟨ rev flatten-zᵣ ⟩)
        )
        ((i₁ ⊗ i₂) ⟨ CM ∙ swap ⟩)
  ⊡ cong 
      (unnest {ss l} _) 
      (sym $ cong (_⟨ swap ⟩) (⊗-combine-remQuot s₁ ((i₁ ⊗ i₂) ⟨ CM ⟩)))
  ⊡ cmfft-icong {_} {_} {_} {twid} _ _ _
      ( sym (proj₁-remQuot-⊕ ((i₁ ⊗ i₂) ⟨ CM ⟩) _ _)
      ⊡ proj₁-remQuot-cong (CM-flatten-comm _ _)
      ⊡ sym (rev-eq {_} {_} {s₂} flatten-zᵣ _)
      ⊡ sym (proj₁-remQuot-⊕ ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ⊕ rev flatten-zᵣ ∙ CM ⟩) _ _)
      ⊡ (proj₁-remQuot-cong $ sym $ ⊕-distributes-∙ {s₁ = s₂} _ {s₁} _ _ _
          ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ⊕ rev flatten-zᵣ ∙ CM ⟩) 
        )
      ) 
  ⊡ cmfft-cong 
      CM 
      dft₁-cong 
      {flatten-z s₂} 
      _ 
      _ 
      (λ β → 
        cong₂ 
          _*_ 
          (   twid-♭ 
                _
                _
            ⊡ cong₂ 
                twid 
                (rev-eq {_} {_} {s₂} flatten-zᵣ β) 
                (sym (proj₂-remQuot-⊕ ((i₁ ⊗ i₂) ⟨ CM ⟩) _ _))
          ) 
          (cmfft-icong 
              {twid = twid} 
              _ 
              _ 
              _ 
              (sym $ proj₂-remQuot-⊕ ((i₁ ⊗ i₂) ⟨ CM ⟩) (rev flatten-zᵣ) (rev flatten-zᵣ) )
          )
      )
      _ 
  ⊡ cong (unnest {l} _) (
      cong _⟨ swap ⟩ (
          ⊗-combine-remQuot _ _
        ⊡ CM-flatten-comm _ _
      )
    )


------------------------------------------------------------------------
-- Currently cmfft is related to nothing... this should fix this...  ---
------------------------------------------------------------------------

CMᵗ-lemma₁ : {s₁ s₂ : S (ss l)} (i₁ : P s₁) (i₂ : P s₂) →
            ((i₁ ⊗ i₂) ⟨ CM ∙ (CMᵗ ⊕ CMᵗ) ⟩) ≡ ((i₁ ⊗ i₂) ⟨ CMᵗ ⟩)
CMᵗ-lemma₁ {l} {s₁} {s₂} i₁ i₂ = ?

  {-
      (
        begin
          (i₁ ⊗ i₂) ⟨ CM ∙ CMᵗ ⊕ CMᵗ ⟩
        ≡⟨ ? ⟩
          (i₁ ⊗ i₂) ⟨ CMᵗ ⟩
        ∎
      )
  -}

cmfft₁≡fft₁ : ∀ {s : S (ss l)}
            → ∀ {dft : {s : S l} → Ar s ℂ → Ar s ℂ}
            → ∀ {twid : ∀ {r : L} → ∀ {s p : S r} → P s → P p → ℂ}
            → ∀ {dft-cong : ∀ {p : S l} → (a b : Ar p ℂ) → (prf : ∀ i → a i ≡ b i) → ∀ i → dft a i ≡ dft b i}
            → ∀ {twid-CM : ∀ {r : L} → ∀ {s p : S (ss r)} → ∀ (i : P s) (j : P p) → twid i j ≡ twid i (j ⟨ CMᵗ ⟩)}
            → ∀ (xs : Ar s ℂ)
            → ∀ (i : P s)
            → cmfft {l} dft twid CM xs i ≡ fft {l} dft twid xs (i ⟨ CMᵗ ⟩)
cmfft₁≡fft₁ {l} {ι _} _ (ι _) = refl
cmfft₁≡fft₁ {l} {s₁ ⊗ s₂} {dft₁} {twid} {dft₁-cong} {twid-CM} xs (i₁ ⊗ i₂) =
  begin 
    cmfft dft₁ twid CM xs (i₁ ⊗ i₂)
  ≡⟨⟩
    unnest {l}
      (λ i → 
        cmfft dft₁ twid CM
          (λ j → twid j i * cmfft dft₁ twid CM (λ j₁ → xs (j₁ ⊗ j)) i)
      )
      ((i₁ ⊗ i₂) ⟨ CM ∙ swap ⟩)
  ≡⟨ remQuot-splits-proof 
      {_} {_} {_} {_} 
      {unnest {l} _} 
      {unnest {l} _}
      (λ j₁ j₂ → 
          cmfft₁≡fft₁ {twid = twid} {dft₁-cong} {twid-CM} _ j₂
        ⊡ fft-cong 
            dft₁-cong 
            {s₂} 
            _ 
            _ 
            (λ β → 
              cong₂ 
                _*_
                refl
                (cmfft₁≡fft₁ {twid = twid} {dft₁-cong} {twid-CM} _ j₁)
            ) 
            (j₂ ⟨ CMᵗ ⟩)
      )
      ((i₁ ⊗ i₂) ⟨ CM ∙ swap ⟩)  
    ⟩
    unnest
      (λ β φ →
         fft dft₁ twid
           (λ α →
                twid α β 
              * fft dft₁ twid (λ j₁ → xs (j₁ ⊗ α)) (β ⟨ CMᵗ ⟩)
           )
           (φ ⟨ CMᵗ ⟩)
      )
      ((i₁ ⊗ i₂) ⟨ CM ∙ swap ⟩)

  ≡⟨ cong 
      (unnest {l} _) 
      (sym $ cong (_⟨ swap ⟩) (⊗-combine-remQuot s₁ ((i₁ ⊗ i₂) ⟨ CM ⟩))) ⟩
    fft 
      dft₁ 
      twid 
      (λ α → 
          twid α (proj₂ (⊗-remQuot s₁ ((i₁ ⊗ i₂) ⟨ CM ⟩))) 
        * fft dft₁ twid (λ δ → xs (δ ⊗ α)) (proj₂ (⊗-remQuot s₁ ((i₁ ⊗ i₂) ⟨ CM ⟩)) ⟨ CMᵗ ⟩)
      ) 
      (proj₁ (⊗-remQuot s₁ ((i₁ ⊗ i₂) ⟨ CM ⟩)) ⟨ CMᵗ ⟩)
  ≡⟨ cong (fft {l} dft₁ twid {s₂} _) 
        ( sym (proj₁-remQuot-⊕ ((i₁ ⊗ i₂) ⟨ CM ⟩) CMᵗ CMᵗ)
        ⊡ proj₁-remQuot-cong {l} {transp s₂} {transp s₁} {(i₁ ⊗ i₂) ⟨ CM ∙ CMᵗ ⊕ CMᵗ ⟩} {(i₁ ⊗ i₂) ⟨ CMᵗ ⟩} (CMᵗ-lemma₁ _ _)
        )
    ⟩
  _ ≡⟨ fft-cong dft₁-cong {s₂} _ _ 
          (λ α → 
            cong₂ _*_
              ( twid-CM α _
              ⊡ cong (twid α) 
                ( sym (proj₂-remQuot-⊕ ((i₁ ⊗ i₂) ⟨ CM ⟩) CMᵗ CMᵗ)
                ⊡ proj₂-remQuot-cong {l} {transp s₂} {transp s₁} {(((i₁ ⊗ i₂) ⟨ CM ⟩) ⟨ CMᵗ ⊕ CMᵗ ⟩)} {(((i₁ ⟨ CMᵗ ⟩) ⊗ (i₂ ⟨ CMᵗ ⟩)) ⟨ CM ⟩)} (CMᵗ-lemma₁ _ _)
                )
              )
              (cong (fft {l} dft₁ twid {s₁} _) (
                ( sym (proj₂-remQuot-⊕ ((i₁ ⊗ i₂) ⟨ CM ⟩) CMᵗ CMᵗ)
                ⊡ proj₂-remQuot-cong {l} {transp s₂} {transp s₁} {(i₁ ⊗ i₂) ⟨ CM ∙ CMᵗ ⊕ CMᵗ ⟩} {(i₁ ⊗ i₂) ⟨ CMᵗ ⟩} (CMᵗ-lemma₁ _ _)
                )
              ))
          ) 
          (proj₁ (⊗-remQuot (transp s₁) (((i₁ ⟨ CMᵗ ⟩) ⊗ (i₂ ⟨ CMᵗ ⟩)) ⟨ CM ⟩))) 
      ⟩
    fft 
      dft₁ 
      twid 
      (λ α → 
          twid α (proj₂ (⊗-remQuot (transp s₁) ((i₁ ⊗ i₂) ⟨ CMᵗ ⟩))) 
        * fft dft₁ twid (λ δ → xs (δ ⊗ α)) (proj₂ (⊗-remQuot (transp s₁) ((i₁ ⊗ i₂) ⟨ CMᵗ ⟩)))
      ) 
      (proj₁ (⊗-remQuot (transp s₁) ((i₁ ⊗ i₂) ⟨ CMᵗ ⟩)))
  ≡⟨ cong 
        (unnest {l} (λ β φ → fft dft₁ twid (λ α → twid α β * fft dft₁ twid (λ δ → xs (δ ⊗ α)) β) φ)) 
        ( cong (_⟨ swap ⟩) ( ⊗-combine-remQuot (transp s₁) ((i₁ ⊗ i₂) ⟨ CMᵗ ⟩))) 
      ⟩
    unnest 
      (λ β φ → 
        fft dft₁ twid 
          (λ α → 
              twid α β 
            * fft dft₁ twid (λ δ → xs (δ ⊗ α)) β
          )
          φ
      )
      ((i₁ ⊗ i₂) ⟨ CMᵗ ∙ swap ⟩)
  ≡⟨⟩
    fft dft₁ twid xs ((i₁ ⊗ i₂) ⟨ CMᵗ ⟩)
  ∎
  












