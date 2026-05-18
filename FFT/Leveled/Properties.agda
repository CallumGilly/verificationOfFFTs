{-# OPTIONS --allow-unsolved-metas #-}

open import Matrix.Mon
open import ComplexNew
open import Matrix.Leveled.Change-Major
open import FFT.Leveled.Specification

module FFT.Leveled.Properties (cplx : Cplx) (M : Mon) (change-major : Change-Major M) (spec : FFT-Specification cplx M change-major) where

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


open Change-Major change-major

CM-flatten-comm : ∀ {s₁ s₂ : S (ss (ss l))}
       → ∀ (i₁ : P s₁)
       → ∀ (i₂ : P s₂)
       →  (i₁ ⊗ i₂) ⟨ CM ∙ rev flatten-zᵣ ⊕ rev flatten-zᵣ ⟩
        ≡
          (i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ⊕ rev flatten-zᵣ ∙ CM ⟩
CM-flatten-comm {l} {s₁} {s₂} i₁ i₂ rewrite rev-eq (_⊕_ {_} {_} {s₂} {s₁} flatten-zᵣ flatten-zᵣ) ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ⊕ rev flatten-zᵣ ∙ CM ⟩)  = refl


cmfft-icong : ∀ {s : S (ss l)}
             → ∀ {dft₁ : {s : S l} → Ar s ℂ → Ar s ℂ}
             → ∀ {twid : ∀ {r : L} → ∀ {s p : S (ss r)} → P s → P p → ℂ}
             → ∀ (xs : Ar s ℂ)
             → ∀ (i j : P s)
             → i ≡ j
             → cmfft dft₁ twid CM xs i ≡ cmfft dft₁ twid CM xs j
cmfft-icong _ _ _ refl = refl

cmfft-dftcong : ∀ {s : S (ss l)} 
              → ∀ {dft₁ dft₂ : {s : S l} → Ar s ℂ → Ar s ℂ}
              → ∀ (dft₁-cong : {s : S l} (a b : P s → ℂ) → ((i : P s) → a i ≡ b i) → (i : P s) → dft₁ a i ≡ dft₁ b i)
              → ∀ (prf : ∀ {s} xs i → dft₁ {s} xs i ≡ dft₂ xs i )
              → ∀ {twid : ∀ {r : L} → ∀ {s p : S (ss r)} → P s → P p → ℂ}
              → ∀ (xs : Ar s ℂ)
              → ∀ (i : P s)
              → cmfft dft₁ twid CM xs i ≡ cmfft dft₂ twid CM xs i
cmfft-dftcong {_} {ι _} _ prf _ (ι _) = prf _ _
cmfft-dftcong {l} {s₁ ⊗ s₂} {dft₁} {dft₂} dft₁-cong prf {twid} xs (i₁ ⊗ i₂) =
      remQuot-splits-proof 
        {xs = unnest _}
        {ys = unnest _}
        (λ α₁ α₂ → 
            cmfft-cong CM dft₁-cong _ _ (λ β → cong (_ *_) (cmfft-dftcong dft₁-cong prf {twid} _ α₁)) α₂
          ⊡ cmfft-dftcong dft₁-cong prf {twid} _ α₂
        )
        ((i₁ ⊗ i₂) ⟨ CM ∙ swap ⟩ )

cmfft₂≡cmfft₁ : ∀ {s : S (ss (ss l))}
     → ∀ {dft : {s : S l} → Ar s ℂ → Ar s ℂ}
     → ∀ {twid : ∀ {r : L} → ∀ {s p : S (ss r)} → P s → P p → ℂ}
     → ∀ {dft-cong : ∀ {p : S l} → (a b : Ar p ℂ) → (prf : ∀ i → a i ≡ b i) → ∀ i → dft a i ≡ dft b i}
     → ∀ {twid-♭ : ∀ {r : L} → ∀ {s p : S (ss (ss r))} → ∀ (i : P s) (j : P p) → twid i j ≡ twid (i ⟨ rev flatten-zᵣ ⟩) (j ⟨ rev flatten-zᵣ ⟩)}
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

-----------------------------------------------------------------------
--- This is a very important lemma, it is currently only proven for ---
--- `Matrix/Simple` in the `cm.agda` file, this proof needs to be   ---
--- converted over to Leveled matrices.                             ---
-----------------------------------------------------------------------

CMᵗ-lemma₁ : {s₁ s₂ : S (ss l)} (i₁ : P s₁) (i₂ : P s₂) →
            ((i₁ ⊗ i₂) ⟨ CM ∙ (CMᵗ ⊕ CMᵗ) ⟩) ≡ ((i₁ ⊗ i₂) ⟨ (CMᵗ ⊕ CMᵗ) ∙ CM ⟩)
CMᵗ-lemma₁ = ?

CMᵗ-lemma₂ : {s₁ s₂ : S (ss l)} (i : P (s₁ ⊗ s₂)) →
            (i ⟨ CM ∙ (CMᵗ ⊕ CMᵗ) ⟩) ≡ (i ⟨ (CMᵗ ⊕ CMᵗ) ∙ CM ⟩)
CMᵗ-lemma₂ (i₁ ⊗ i₂) = CMᵗ-lemma₁ i₁ i₂

cmfft≡fft : ∀ {s : S (ss l)}
            → ∀ {dft : {s : S l} → Ar s ℂ → Ar s ℂ}
            → ∀ {twid : ∀ {r : L} → ∀ {s p : S (ss r)} → P s → P p → ℂ}
            → ∀ {dft-cong : ∀ {p : S l} → (a b : Ar p ℂ) → (prf : ∀ i → a i ≡ b i) → ∀ i → dft a i ≡ dft b i}
            → ∀ {twid-CM : ∀ {r : L} → ∀ {s p : S (ss r)} → ∀ (i : P s) (j : P p) → twid i j ≡ twid i (j ⟨ CMᵗ ⟩)}
            → ∀ (xs : Ar s ℂ)
            → ∀ (i : P s)
            → cmfft {l} dft twid CM xs i ≡ fft {l} dft twid xs (i ⟨ CMᵗ ⟩)
cmfft≡fft {l} {ι _} _ (ι _) = refl
cmfft≡fft {l} {s₁ ⊗ s₂} {dft₁} {twid} {dft₁-cong} {twid-CM} xs (i₁ ⊗ i₂) =
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
          cmfft≡fft {twid = twid} {dft₁-cong} {twid-CM} _ j₂
        ⊡ fft-cong 
            dft₁-cong 
            {s₂} 
            _ 
            _ 
            (λ β → 
              cong₂ 
                _*_
                refl
                (cmfft≡fft {twid = twid} {dft₁-cong} {twid-CM} _ j₁)
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
  
fft≡cmfft : ∀ {s : S (ss l)}
            → ∀ {dft : {s : S l} → Ar s ℂ → Ar s ℂ}
            → ∀ {twid : ∀ {r : L} → ∀ {s p : S (ss r)} → P s → P p → ℂ}
            → ∀ {dft-cong : ∀ {p : S l} → (a b : Ar p ℂ) → (prf : ∀ i → a i ≡ b i) → ∀ i → dft a i ≡ dft b i}
            → ∀ {twid-CM : ∀ {r : L} → ∀ {s p : S (ss r)} → ∀ (i : P s) (j : P p) → twid i j ≡ twid i (j ⟨ CMᵗ ⟩)}
            → ∀ (xs : Ar s ℂ)
            → ∀ (i : P s)
            → fft {l} dft twid xs (i ⟨ CMᵗ ⟩) ≡ cmfft {l} dft twid CM xs i
fft≡cmfft {l} {s} {dft₁} {twid} {dft-cong₁} {twid-CM} xs i = sym (cmfft≡fft {l} {s} {dft₁} {twid} {dft-cong₁} {twid-CM} xs i)

-- We can now relate any fft to cmfft, and any level cmfft to the level below it

pre-ufft-congᵗ : {n : S (ss zz)} (a : Ar n ℂ) (b : P n → ℂ) →
                 ((i : P n) → a i ≡ b i) →
                 (i : P n) →
                 reshape CMᵗ
                 (pre-ufft dft (λ j₁ → twiddles (j₁ ⟨ transpᵣ ⟩))
                  (reshape (rev transpᵣ) a))
                 i
                 ≡
                 reshape CMᵗ
                 (pre-ufft dft (λ j₁ → twiddles (j₁ ⟨ transpᵣ ⟩))
                  (reshape (rev transpᵣ) b))
                 i
pre-ufft-congᵗ a b prf i 
    = pre-ufft-cong dft-cong (reshape (rev transpᵣ) a) (reshape (rev transpᵣ) b) (λ i → prf (i ⟨ rev transpᵣ ⟩)) (i ⟨ CMᵗ ⟩)

pre-ufft≡dft : {s : S (ss zz)}
               (xs : Ar s ℂ) (i : P s) →
               reshape CMᵗ
               (pre-ufft dft (λ j₁ → twiddles (j₁ ⟨ transpᵣ ⟩))
                (reshape (rev transpᵣ) xs))
               i
               ≡ reshape (rev flatten-zᵣ) (dft (reshape flatten-zᵣ xs)) i
pre-ufft≡dft {s} xs i =
        pre-ufft≡fft {twid = twiddles} (twiddles-transₗ-lemma _ _) dft-cong xs (i ⟨ CMᵗ ⟩)
      ⊡ sym (dft≡fft _ i)
               
pre-ufft≡cmfft : {s : S (ss zz)}
               (xs : Ar s ℂ) (i : P s) →
               reshape CMᵗ
               (pre-ufft dft (λ j₁ → twiddles (j₁ ⟨ transpᵣ ⟩))
                (reshape (rev transpᵣ) xs))
               i
               ≡ cmfft {zz} dft twiddles CM {s} xs i
pre-ufft≡cmfft {s} xs i =
        pre-ufft≡fft {twid = twiddles} (twiddles-transₗ-lemma _ _) dft-cong xs (i ⟨ CMᵗ ⟩)
      ⊡ fft≡cmfft {twid = twiddles} {dft-cong} {λ _ _ → sym (twiddles-CMᵗᵣ-lemma _ _)} xs i

fftn : ∀ {s : S (ss (ss zz))} → Ar s ℂ → Ar s ℂ
fftn {s} xs = reshape (CMᵗ ∙ rev transpᵣ)
            ( post-ufft (reshape CMᵗ
                        ∘ pre-ufft dft (λ j₁ j₂ → twiddles (j₁ ⟨ transpᵣ ⟩) j₂) 
                        ∘ reshape (rev transpᵣ)
                        )
                        (λ j₁ j₂ → twiddles j₁ (j₂ ⟨ transpᵣ ⟩)) {s} xs)

-- Big mamma: 
-- Note: This could probably be generalised over level L, I would just need to
--       generalise a few of the proofs it depends on :)
-- Note 2: The above note is silly, given fftn is defined for level 2, I could
--         redefine that generally and require that it be parsed the level l's 
--         dft, but I don't think that same structure would be used at higher 
--         levels 
fftn≡dft : ∀ {s : S (ss (ss zz))} 
         → ∀ (xs : Ar s ℂ)
         → ∀ (i : P s)
         → fftn xs i ≡ dft (reshape (flatten-zᵣ ∙ flatten-zᵣ) xs) (i ⟨ rev flatten-zᵣ ∙ rev flatten-zᵣ ⟩)
fftn≡dft {ι s} xs (ι i) = pre-ufft≡dft {s} (reshape flatten-zᵣ xs) _
fftn≡dft {s₁ ⊗ s₂} xs (i₁ ⊗ i₂) =
  begin
    fftn xs (i₁ ⊗ i₂)
  ≡⟨⟩
    unnest 
      (λ α → 
        post-ufft 
          _
          (λ j₁ j₂ → twiddles j₁ (j₂ ⟨ transpᵣ ⟩)) 
          (λ β → 
              twiddles β (α ⟨ transpᵣ ⟩) 
            * post-ufft 
                _ 
                (λ j₁ j₂ → twiddles j₁ (j₂ ⟨ transpᵣ ⟩)) 
                (λ δ → xs (δ ⊗ β)) 
                α
          )
      ) 
      ((i₁ ⊗ i₂) ⟨ CMᵗ ∙ rev transpᵣ ⟩)
  -- Reduce outer UFFT to FFT
  ≡⟨ remQuot-splits-proof 
        {xs = unnest _}
        {unnest _}
        (λ α₁ α₂ → 
            post-ufft≡fft {_} {_} {twiddles} pre-ufft-congᵗ _ α₂
          ⊡ (fft-cong pre-ufft-congᵗ _ _ 
                (λ β → 
                  cong₂ _*_
                    refl
                    (post-ufft≡fft {twid = twiddles} pre-ufft-congᵗ _ α₁)
                ) 
                (α₂ ⟨ transpᵣ ⟩)
            )
        )
        ((i₁ ⊗ i₂) ⟨ CMᵗ ∙ rev transpᵣ ⟩) 
   ⟩
      unnest 
        (λ z z₁ → 
          fft {ss zz} 
            _ 
            twiddles 
            {s₂}
            (λ z₂ → 
                twiddles z₂ (z ⟨ transpᵣ ⟩) 
              * fft {ss zz} 
                  _
                  twiddles 
                  (λ δ → xs (δ ⊗ z₂)) 
                  (z ⟨ transpᵣ ⟩)
            ) 
            (z₁ ⟨ transpᵣ ⟩)
        ) 
        ((i₁ ⊗ i₂) ⟨ CMᵗ ∙ rev transpᵣ ⟩)
  -- Replace FFT with CMFFT so we can work over levels
  ≡⟨ remQuot-splits-proof
      {xs = unnest _}
      {unnest _}
      (λ α₁ α₂ → 
            cong (fft {ss zz} _ twiddles {s₂} _) (sym (rev-eq′ CMᵗ _))
          ⊡ fft≡cmfft {_} {_} {_} {twiddles} {pre-ufft-congᵗ} {λ _ _ → sym (twiddles-CMᵗᵣ-lemma _ _)} _ (α₂ ⟨ transpᵣ ∙ rev CMᵗ ⟩)
          ⊡ cmfft-cong CM pre-ufft-congᵗ _ _
              (λ β → 
                cong₂ _*_
                  refl
                  ( cong (fft {ss zz} _ twiddles {s₁} _) (sym (rev-eq′ CMᵗ _))
                  ⊡ fft≡cmfft {_} {_} {_} {twiddles} {pre-ufft-congᵗ} {λ _ _ → sym (twiddles-CMᵗᵣ-lemma _ _)} _ (α₁ ⟨ transpᵣ ∙ rev CMᵗ ⟩)
                  )
              )
              (α₂ ⟨ transpᵣ ∙ rev CMᵗ ⟩)
      )
      ((i₁ ⊗ i₂) ⟨ CMᵗ ∙ rev transpᵣ ⟩)
    ⟩
  -- Replace inner pre-ufft with fft
  _ ≡⟨ remQuot-splits-proof
        {xs = unnest _}
        {unnest _}
        ( λ α₁ α₂ →
            cmfft-cong CM pre-ufft-congᵗ {s₂} _ _ 
              (λ β → 
                cong (_ *_) $
                  cmfft-dftcong pre-ufft-congᵗ pre-ufft≡cmfft {twiddles} _ (α₁ ⟨ transpᵣ ∙ rev CMᵗ ⟩)
              )
              (α₂ ⟨ transpᵣ ∙ rev CMᵗ ⟩ )
          ⊡ cmfft-dftcong pre-ufft-congᵗ pre-ufft≡cmfft {twiddles} _ (α₂ ⟨ transpᵣ ∙ rev CMᵗ ⟩)
        )
        ((i₁ ⊗ i₂) ⟨ CMᵗ ∙ rev transpᵣ ⟩)
      ⟩
        unnest 
          (λ α₁ α₂ → 
            cmfft 
              (cmfft dft twiddles CM) 
              twiddles 
              CM 
              (λ β → 
                  twiddles β (α₁ ⟨ transpᵣ ⟩) 
                * cmfft 
                    (cmfft dft twiddles CM) 
                    twiddles 
                    CM 
                    (λ δ → xs (δ ⊗ β)) 
                    (α₁ ⟨ transpᵣ ∙ rev CMᵗ ⟩)
              ) 
              (α₂ ⟨ transpᵣ ∙ rev CMᵗ ⟩)
          ) 
          ((i₁ ⊗ i₂) ⟨ CMᵗ ∙ rev transpᵣ ⟩ )
  ≡⟨ remQuot-splits-proof 
        {xs = unnest _}
        {unnest _}
        (λ α₁ α₂ → 
            cmfft₂≡cmfft₁ {_} {_} {_} {twiddles} {dft-cong} {λ _ _ → sym (twiddles-rev-flatten-zᵣ-lemma _ _)} _ (α₂ ⟨ transpᵣ ∙ rev CMᵗ ⟩)
          ⊡ cmfft-cong
              CM 
              dft-cong 
              _ 
              _
              (λ β →
                cong (_ *_)
                  (cmfft₂≡cmfft₁ {_} {_} {_} {twiddles} {dft-cong} {λ _ _ → sym (twiddles-rev-flatten-zᵣ-lemma _ _)} _ (α₁ ⟨ transpᵣ ∙ rev CMᵗ ⟩))
              )
              (α₂ ⟨ transpᵣ ∙ rev CMᵗ ∙ rev flatten-zᵣ ⟩ )
        )
        ((i₁ ⊗ i₂) ⟨ CMᵗ ∙ rev transpᵣ ⟩ )
    ⟩
        unnest 
          (λ α₁ α₂ → 
            cmfft 
              {zz}
              dft 
              twiddles 
              CM 
              (λ β →
                  twiddles (β ⟨ flatten-zᵣ ⟩) (α₁ ⟨ transpᵣ ⟩) 
                * cmfft
                    {zz}
                    dft
                    twiddles
                    CM
                    (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                    (α₁ ⟨ transpᵣ ∙ rev CMᵗ ∙ rev flatten-zᵣ ⟩)
              )
              (α₂ ⟨ transpᵣ ∙ rev CMᵗ ∙ rev flatten-zᵣ ⟩)
          )
          ((i₁ ⊗ i₂) ⟨ CMᵗ ∙ rev transpᵣ ⟩ )
  ≡⟨ unnest-transp-lemma ((i₁ ⊗ i₂) ⟨ CMᵗ ⟩) _ ⟩
        unnest 
          (λ α₂ α₁ → 
            cmfft 
              {zz}
              dft 
              twiddles 
              CM 
              (λ β →
                  twiddles (β ⟨ flatten-zᵣ ⟩) (α₁ ⟨ rev transpᵣ ∙ transpᵣ ⟩) 
                * cmfft
                    {zz}
                    dft
                    twiddles
                    CM
                    (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                    (α₁ ⟨ rev transpᵣ ∙ transpᵣ ∙ rev CMᵗ ∙ rev flatten-zᵣ ⟩)
              )
              (α₂ ⟨ rev transpᵣ ∙ transpᵣ ∙ rev CMᵗ ∙ rev flatten-zᵣ ⟩)
          )
          ((i₁ ⊗ i₂) ⟨ CMᵗ ⟩ )
  ≡⟨ remQuot-splits-proof 
      {xs = unnest _}
      {unnest _}
      (λ α₁ α₂ → 
        cmfft-icong {_} {_} {_} {twiddles} _ 
            ((((α₁ ⟨ rev transpᵣ ⟩) ⟨ transpᵣ ⟩) ⟨ rev CMᵗ ⟩) ⟨ rev flatten-zᵣ ⟩)
            ((α₁ ⟨ rev CMᵗ ⟩) ⟨ rev flatten-zᵣ ⟩) 
            (cong (_⟨ rev flatten-zᵣ ⟩) (cong (_⟨ rev CMᵗ ⟩) (rev-eq′ transpᵣ α₁)))
        ⊡ cmfft-cong _ dft-cong _ _ (λ β → 
            cong₂
              _*_
              (cong (twiddles _) (rev-eq′ transpᵣ α₂))
              (cmfft-icong {_} {_} {_} {twiddles} _ 
                ((((α₂ ⟨ rev transpᵣ ⟩) ⟨ transpᵣ ⟩) ⟨ rev CMᵗ ⟩) ⟨ rev flatten-zᵣ
             ⟩) 
                ((α₂ ⟨ rev CMᵗ ⟩) ⟨ rev flatten-zᵣ ⟩) 
                (cong (_⟨ rev flatten-zᵣ ⟩) (cong (_⟨ rev CMᵗ ⟩) (rev-eq′ transpᵣ α₂)))
              )
          ) (α₁ ⟨ rev CMᵗ ∙ rev flatten-zᵣ ⟩)
      )
      ((i₁ ⊗ i₂) ⟨ CMᵗ ⟩)  
    ⟩ -- reveq × 3
      unnest 
          (λ α₁ α₂ → 
            cmfft 
              {zz}
              dft 
              twiddles 
              CM 
              (λ β →
                  twiddles (β ⟨ flatten-zᵣ ⟩) α₂
                * cmfft
                    {zz}
                    dft
                    twiddles
                    CM
                    (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                    (α₂ ⟨ rev CMᵗ ∙ rev flatten-zᵣ ⟩)
              )
              (α₁ ⟨ rev CMᵗ ∙ rev flatten-zᵣ ⟩)
          )
          ((i₁ ⊗ i₂) ⟨ CMᵗ ⟩)
  ≡⟨ unnest-⊕-rev-lemma ((i₁ ⊗ i₂) ⟨ CMᵗ ⟩) (rev CMᵗ ∙ rev flatten-zᵣ) (rev CMᵗ ∙ rev flatten-zᵣ) _ ⟩ -- Pull (rev CMᵗ ∙ rev flatten-zᵣ) out of unnest, twiddles needs some fixing in the process
      unnest 
          (λ α₁ α₂ → 
            cmfft 
              {zz}
              dft 
              twiddles 
              CM 
              (λ β →
                  twiddles (β ⟨ flatten-zᵣ ⟩) (α₂ ⟨ rev (rev CMᵗ ∙ rev flatten-zᵣ) ⟩)
                * cmfft
                    {zz}
                    dft
                    twiddles
                    CM
                    (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                    (α₂ ⟨ rev (_∙_ {p = s₁} (rev CMᵗ) (rev flatten-zᵣ)) ∙ (rev CMᵗ ∙ rev flatten-zᵣ) ⟩)
              )
              (α₁ ⟨ rev (_∙_ {p = s₂} (rev CMᵗ) (rev flatten-zᵣ)) ∙ (rev CMᵗ ∙ rev flatten-zᵣ) ⟩)
          )
          ((i₁ ⊗ i₂) ⟨ CMᵗ ∙ ((rev CMᵗ ∙ rev flatten-zᵣ) ⊕ (rev CMᵗ ∙ rev flatten-zᵣ)) ⟩)
  ≡⟨ remQuot-splits-proof 
      {xs = unnest _}
      {unnest _}
      (λ α₁ α₂ → 
          cmfft-icong {_} {_} {dft} {twiddles} _ (α₁ ⟨ rev (_∙_ {p = s₂} (rev CMᵗ) (rev flatten-zᵣ)) ∙ (rev CMᵗ ∙ rev flatten-zᵣ) ⟩) α₁ (rev-eq′ (_∙_ {p = s₂} (rev CMᵗ) (rev flatten-zᵣ)) α₁)
        ⊡ cmfft-cong CM dft-cong _ _ (λ β → cong₂ _*_ refl (cmfft-icong {_} {_} {dft} {twiddles} _ (α₂ ⟨ rev (_∙_ {p = s₁} (rev CMᵗ) (rev flatten-zᵣ)) ∙ (rev CMᵗ ∙ rev flatten-zᵣ) ⟩) α₂ (rev-eq′ (_∙_ {p = s₁} (rev CMᵗ) (rev flatten-zᵣ)) α₂))) α₁
      ) 
      ((i₁ ⊗ i₂) ⟨ CMᵗ ∙ ((rev CMᵗ ∙ rev flatten-zᵣ) ⊕ (rev CMᵗ ∙ rev flatten-zᵣ)) ⟩)
    ⟩
      unnest 
          (λ α₁ α₂ → 
            cmfft 
              {zz}
              dft 
              twiddles 
              CM 
              (λ β →
                  twiddles (β ⟨ flatten-zᵣ ⟩) (α₂ ⟨ rev (rev CMᵗ ∙ rev flatten-zᵣ) ⟩)
                * cmfft
                    {zz}
                    dft
                    twiddles
                    CM
                    (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                    α₂
              )
              α₁
          )
          ((i₁ ⊗ i₂) ⟨ CMᵗ ∙ ((rev CMᵗ ∙ rev flatten-zᵣ) ⊕ (rev CMᵗ ∙ rev flatten-zᵣ)) ⟩)
  ≡⟨⟩
      unnest 
          (λ α₁ α₂ → 
            cmfft 
              {zz}
              dft 
              twiddles 
              CM 
              (λ β →
                  twiddles (β ⟨ flatten-zᵣ ⟩) (α₂ ⟨ rev (rev CMᵗ ∙ rev flatten-zᵣ) ⟩)
                * cmfft
                    {zz}
                    dft
                    twiddles
                    CM
                    (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                    α₂
              )
              α₁
          )
          ((i₁ ⊗ i₂) ⟨ (CMᵗ ⊕ CMᵗ ∙ CM) ∙ ((rev CMᵗ ∙ rev flatten-zᵣ) ⊕ (rev CMᵗ ∙ rev flatten-zᵣ)) ⟩)
  ≡⟨ cong (unnest _) (cong (_⟨ ((rev CMᵗ ∙ rev flatten-zᵣ) ⊕ (rev CMᵗ ∙ rev flatten-zᵣ)) ⟩) (sym (CMᵗ-lemma₁ i₁ i₂))) ⟩ -- (CMᵗ ⊕ CMᵗ ∙ CM) ≡ CM ∙ CMᵗ ⊕ CMᵗ 
      unnest 
          (λ α₁ α₂ → 
            cmfft 
              {zz}
              dft 
              twiddles 
              CM 
              (λ β →
                  twiddles (β ⟨ flatten-zᵣ ⟩) (α₂ ⟨ rev (rev CMᵗ ∙ rev flatten-zᵣ) ⟩)
                * cmfft
                    {zz}
                    dft
                    twiddles
                    CM
                    (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                    α₂
              )
              α₁
          )
          ((i₁ ⊗ i₂) ⟨ CM ∙ CMᵗ ⊕ CMᵗ ∙ ((rev CMᵗ ∙ rev flatten-zᵣ) ⊕ (rev CMᵗ ∙ rev flatten-zᵣ)) ⟩)
  ≡⟨ cong (unnest _) (sym (⊕-distributes-∙ _ _ _ _ ((i₁ ⊗ i₂) ⟨ CM ∙ CMᵗ ⊕ CMᵗ ⟩))) ⟩ -- (a ∙ b) ⊕ (c ∙ d) ≡ (a ⊕ c) ∙ (b ⊕ d)
      unnest 
          (λ α₁ α₂ → 
            cmfft 
              {zz}
              dft 
              twiddles 
              CM 
              (λ β →
                  twiddles (β ⟨ flatten-zᵣ ⟩) (α₂ ⟨ rev (rev CMᵗ ∙ rev flatten-zᵣ) ⟩)
                * cmfft
                    {zz}
                    dft
                    twiddles
                    CM
                    (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                    α₂
              )
              α₁
          )
          ((i₁ ⊗ i₂) ⟨ CM ∙ CMᵗ ⊕ CMᵗ ∙ (rev CMᵗ ⊕ rev CMᵗ) ∙ (rev flatten-zᵣ ⊕ rev flatten-zᵣ) ⟩)
  ≡⟨ 
        cong (unnest _) (cong (_⟨ rev flatten-zᵣ ⊕ rev flatten-zᵣ ⟩) (
            (⊕-distributes-∙ _ _ _ _ ((i₁ ⊗ i₂) ⟨ CM ⟩))
          ⊡ (⊕-rev-eq-lemma ((i₁ ⊗ i₂) ⟨ CM ⟩) _ _)
        ))
    ⟩ -- Rev eq 
      unnest 
          (λ α₁ α₂ → 
            cmfft 
              {zz}
              dft 
              twiddles 
              CM 
              (λ β →
                  twiddles (β ⟨ flatten-zᵣ ⟩) (α₂ ⟨ rev (rev CMᵗ ∙ rev flatten-zᵣ) ⟩)
                * cmfft
                    {zz}
                    dft
                    twiddles
                    CM
                    (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                    α₂
              )
              α₁
          )
          ((i₁ ⊗ i₂) ⟨ CM ∙ (rev flatten-zᵣ ⊕ rev flatten-zᵣ) ⟩)
  ≡⟨⟩ 
      unnest 
          (λ α₁ α₂ → 
            cmfft 
              {zz}
              dft 
              twiddles 
              CM 
              (λ β →
                  twiddles (β ⟨ flatten-zᵣ ⟩) (α₂ ⟨ rev (rev CMᵗ ∙ rev flatten-zᵣ) ⟩)
                * cmfft
                    {zz}
                    dft
                    twiddles
                    CM
                    (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                    α₂
              )
              α₁
          )
          ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ∙ CM ∙ (_∙_ {p = s₂ ⊗ s₁} flatten-zᵣ (rev flatten-zᵣ)) ⟩)
  ≡⟨ remQuot-splits-proof 
      {xs = unnest _}
      {unnest _}
      (λ α₁ α₂ → 
        cmfft-cong CM dft-cong _ _
          (λ β → 
            cong₂ _*_ 
              ( cong (twiddles _) (rev-rev CMᵗ (α₂ ⟨ rev (rev flatten-zᵣ) ⟩))
              ⊡ twiddles-CMᵗᵣ-lemma _ _
              ⊡ cong (twiddles _) (rev-rev flatten-zᵣ α₂)
              ⊡ twiddles-flatten-zᵣ-lemma β α₂
              ) 
              refl
          ) 
          α₁
      )
      ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ∙ CM ∙ (_∙_ {p = s₂ ⊗ s₁} flatten-zᵣ (rev flatten-zᵣ)) ⟩)
    ⟩ -- Twiddle fuckery
      unnest 
          (λ α₁ α₂ → 
            cmfft 
              {zz}
              dft 
              twiddles 
              CM 
              (λ β →
                  twiddles β α₂
                * cmfft
                    {zz}
                    dft
                    twiddles
                    CM
                    (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                    α₂
              )
              α₁
          )
          ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ∙ CM ∙ (_∙_ {p = s₂ ⊗ s₁} flatten-zᵣ (rev flatten-zᵣ)) ⟩)
  ≡⟨ cong (unnest _) (rev-eq {_} {_} {s₂ ⊗ s₁} {_} flatten-zᵣ ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ∙ CM ⟩)) ⟩ -- flatten-zᵣ ∙ rev flatten-zᵣ ≡ eq
      unnest 
        (λ α₁ α₂ → cmfft 
          {zz}
          dft 
          twiddles 
          CM
          (λ β → 
              twiddles β α₂ 
            * cmfft 
                {zz}
                dft 
                twiddles 
                CM
                (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                α₂ 
          ) α₁ 
        ) 
        ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ∙ CM ⟩) 
  ≡⟨ remQuot-splits-proof 
      {xs = unnest _}
      {unnest _}
      (λ α₁ α₂ → 
          cmfft-icong {_} {_} {dft} {twiddles} _ α₁ (α₁ ⟨ CMᵗ ∙ rev CMᵗ ⟩) (sym (rev-eq CMᵗ α₁))
        ⊡ cmfft-cong CM dft-cong _ _ (λ β → 
            cong₂ _*_ 
              (sym (twiddles-CMᵗᵣ-lemma _ _)) -- Twiddle fuckery
              (cmfft-icong {_} {_} {dft} {twiddles} _ α₂ (α₂ ⟨ CMᵗ ∙ rev CMᵗ ⟩) (sym (rev-eq CMᵗ α₂)))
          ) (α₁ ⟨ CMᵗ ∙ rev CMᵗ ⟩)
      ) 
      ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ∙ CM ⟩) 
    ⟩ -- Bottom up, rev-eq×2 & twiddle _ i ≡ twiddle _ (i ⟨ CMᵗ ⟩)
      unnest 
        (λ α₁ α₂ → cmfft 
          {zz}
          dft 
          twiddles 
          CM
          (λ β → 
              twiddles β (α₂ ⟨ CMᵗ ⟩)
            * cmfft 
                {zz}
                dft 
                twiddles 
                CM
                (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                (α₂ ⟨ CMᵗ ∙ rev CMᵗ ⟩)
          ) (α₁ ⟨ CMᵗ ∙ rev CMᵗ ⟩)
        ) 
        ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ∙ CM ⟩) 
  ≡⟨ unnest-⊕-lemma ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ∙ CM ⟩) CMᵗ CMᵗ _ ⟩ -- Bottom up, Push CMᵗ inside
      unnest 
        (λ α₁ α₂ → cmfft 
          {zz}
          dft 
          twiddles 
          CM
          (λ β → 
              twiddles β α₂
            * cmfft 
                {zz}
                dft 
                twiddles 
                CM
                (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                (α₂ ⟨ rev CMᵗ ⟩)
          ) (α₁ ⟨ rev CMᵗ ⟩)
        ) 
        ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ∙ CM ∙ (CMᵗ ⊕ CMᵗ) ⟩) 
  ≡⟨ cong (unnest _) (CMᵗ-lemma₂ ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ⟩)) ⟩ -- Bottom up, (CMᵗ ⊕ CMᵗ) ∙ CM ≡ CM ∙ (CMᵗ ⊕ CMᵗ)
      unnest 
        (λ α₁ α₂ → cmfft 
          {zz}
          dft 
          twiddles 
          CM
          (λ β → 
              twiddles β α₂
            * cmfft 
                {zz}
                dft 
                twiddles 
                CM
                (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                (α₂ ⟨ rev CMᵗ ⟩)
          ) (α₁ ⟨ rev CMᵗ ⟩)
        ) 
        ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ∙ (CMᵗ ⊕ CMᵗ) ∙ CM ⟩) 
  -- Go back from CMFFT to FFT
  ≡⟨ remQuot-splits-proof 
        {xs = unnest _}
        {unnest _}
        (λ α₁ α₂ → 
            cmfft-cong CM dft-cong _ _ 
              (λ β → 
                cong₂ _*_
                  refl
                  ( cmfft≡fft {_} {_} {_} {twiddles} {dft-cong} {λ i j → sym (twiddles-CMᵗᵣ-lemma i j)} _ (α₂ ⟨ rev CMᵗ ⟩)
                  ⊡ cong (fft {zz} dft twiddles {flatten-z s₁} _) (rev-eq′ CMᵗ α₂)
                  )
              ) 
              (α₁ ⟨ rev CMᵗ ⟩)
          ⊡ cmfft≡fft {_} {_} {_} {twiddles} {dft-cong} {λ _ _ → sym (twiddles-CMᵗᵣ-lemma _ _)} _ (α₁ ⟨ rev CMᵗ ⟩)
          ⊡ cong (fft {zz} dft twiddles {flatten-z s₂} _) (rev-eq′ CMᵗ α₁)
        )
        ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ∙ CMᵗ ⟩)
     ⟩
      unnest 
        (λ α₁ α₂ → fft 
          dft 
          twiddles 
          (λ β → 
              twiddles β α₂
            * fft 
                dft 
                twiddles 
                (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                α₂
          ) α₁
        ) 
        ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ∙ CMᵗ ⟩) 
    ≡⟨ sym (unnest-swap-lemma ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ∙ (CMᵗ ⊕ CMᵗ) ∙ CM ⟩) _) ⟩
      unnest 
        (λ α₁ α₂ → fft 
          dft 
          twiddles 
          (λ β → 
              twiddles β α₁
            * fft 
                dft 
                twiddles 
                (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                α₁
          ) α₂
        ) 
        ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ∙ (CMᵗ ⊕ CMᵗ) ∙ CM ∙ swap ⟩) 
  -- Relate the FFT back to the DFT
  ≡⟨ sym (dft≡fft {_} (reshape flatten-zᵣ xs) ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ⟩)) ⟩
    dft (reshape (flatten-zᵣ ∙ flatten-zᵣ) xs) ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ∙ rev flatten-zᵣ ⟩)
  ∎

