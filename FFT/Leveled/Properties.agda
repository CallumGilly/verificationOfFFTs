open import Matrix.Mon
open import ComplexNew
open import Matrix.Leveled.Change-Major
open import FFT.Leveled.Specification

open import Matrix.NatMon

module FFT.Leveled.Properties (cplx : Cplx)  (spec : FFT-Specification cplx ℕ-Mon ?) where

--(cm : Change-Major ℕ-Mon)

--open Change-Major cm
open FFT-Specification spec
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning

open Cplx cplx

open Mon ℕ-Mon
open import Matrix.Leveled.Base ℕ-Mon
open import Matrix.Leveled.Reshape ℕ-Mon

open import FFT.Leveled.FFT cplx ℕ-Mon
open import FFT.Leveled.UFFT cplx ℕ-Mon

open import Function 
open import Data.Product hiding (swap; map)
open import Data.Product.Properties


private 
  infixl 4 _⊡_
  _⊡_ = trans
  variable 
    l : L


module fl where
  StripSzz : S zz → U
  StripSzz (ν x) = x

  StripSzz-id : ∀ {s : S zz} → Reshape s (ν (StripSzz s))
  StripSzz-id {ν x} = eq

  flatten-z : S (ss l) → S l
  flatten-z {l} (ι x) = x
  flatten-z {zz} (x ⊗ y) = ν (StripSzz (flatten-z x) ● StripSzz (flatten-z y))
  flatten-z {ss l} (x ⊗ y) = (flatten-z x) ⊗ (flatten-z y)

  flatten-zᵣ : ∀ {s : S (ss l)} → Reshape s (flatten-z s)
  flatten-zᵣ {l} {ι s} = down eq
  flatten-zᵣ {zz} {s ⊗ s₁} = flat ∙ ((up StripSzz-id ∙ flatten-zᵣ) ⊕ (up StripSzz-id ∙ flatten-zᵣ))
  flatten-zᵣ {ss l} {s ⊗ s₁} = flatten-zᵣ ⊕ flatten-zᵣ
open fl

open import Data.Nat.Properties

ν-helper : ∀ {s} {p} →
           (StripSzz (flatten-z s) ● StripSzz (flatten-z p)) ≡
           (StripSzz (flatten-z p) ● StripSzz (flatten-z s))
ν-helper {s} {p} = comm {StripSzz (flatten-z s)} {_}

Change-Major-ℕ : Change-Major ℕ-Mon
Change-Major.CM Change-Major-ℕ {zz  } {s} {p} = (rev flatten-zᵣ) 
                                              ∙ subst (λ t → Reshape (flatten-z (s ⊗ p)) (ν t)) (comm {StripSzz (flatten-z s)} {_}) eq 
                                              ∙ flatten-zᵣ
Change-Major.CM Change-Major-ℕ {ss l} {s} {p} = (rev flatten-zᵣ) 
                                              ∙ CM {l}
                                              ∙ flatten-zᵣ
                                      where 
                                        open Change-Major Change-Major-ℕ

open Change-Major Change-Major-ℕ

ext-cong-app : 
    ∀ {X : Set}
  → ∀ {s  : S l}
  → ∀ {xs ys : Ar s X}
  → ∀ (prf : ∀ j → xs j ≡ ys j)
  → ∀ i → xs i ≡ ys i
ext-cong-app prf i = prf i

lemma : 
      ∀ {X : Set}
    → ∀ {s p : S (ss l)}
    → ∀ {xs ys : Ar (p ⊗ s) X}
    → ∀ (prf : ∀ (i : P (s ⊗ p)) → xs (i ⟨ swap ⟩) ≡ ys (i ⟨ swap ⟩) )
    → ∀ (i : P (s ⊗ p)) → xs (i ⟨ CM ⟩) ≡ ys (i ⟨ CM ⟩)
lemma {_} {X} {s} {p} {xs} {ys} prf (i₁ ⊗ i₂) = ext-cong-app {_} {_} {_} {xs} {ys} (λ{ (a ⊗ b) → prf (b ⊗ a)}) ((i₁ ⊗ i₂) ⟨ CM ⟩)


tma : ∀ {X : Set}
    → ∀ {s : S l}
    → ∀ {xs ys : Ar (transp s) X}
    → ∀ (prf : ∀ (i : P (transp s)) → xs i ≡ ys i )
    → ∀ (i : P s) → xs (i ⟨ CMᵗ ⟩) ≡ ys (i ⟨ CMᵗ ⟩)
tma {.zz} {_} {ν _} prf i@(ν _) = prf i
tma {.(ss _)} {_} {ι s} {xs} {ys} prf i@(ι _) = prf i
tma {.(ss _)} {_} {s₁ ⊗ s₂} {xs} {ys} prf (i₁ ⊗ i₂) = ext-cong-app {_} {_} {_} {xs} {ys} (λ{ (a ⊗ b) → prf (a ⊗ b) }) ((i₁ ⊗ i₂) ⟨ CMᵗ ⟩)

remove-reshape : 
      ∀ {X : Set}
    → ∀ {s p : S l}
    → ∀ {xs ys : Ar s X}
    → ∀ {resh : Reshape s p}
    → ∀ (prf : ∀ (i : P s) → xs i ≡ ys i)
    → ∀ (i : P p) → xs (i ⟨ resh ⟩) ≡ ys (i ⟨ resh ⟩)
remove-reshape {l} {X} {s} {p} {xs} {ys} {resh} prf i = prf (i ⟨ resh ⟩)

{- Don't think this one is true...
remove-reshape-lvl : 
      ∀ {X : Set}
    → ∀ {l r : L}
    → ∀ {s : S l}
    → ∀ {p : S r}
    → ∀ {xs : Ar s X}
    → ∀ {ys : Ar p X}
    → ∀ {resh₁ : Reshape p s}
    → ∀ {resh₂ : Reshape p s}
    → ∀ (prf : ∀ (i : P s) → xs i ≡ ys (i ⟨ resh₁ ⟩))
    →          ∀ (i : P s) → xs i ≡ ys (i ⟨ resh₂ ⟩) 
remove-reshape-lvl {X} {l} {r} {s} {p} {xs} {ys} {resh₁} {resh₂} prf i = ?
-}



--CM : ∀ {s p : S (ss l)} → Reshape (s ⊗ p) (p ⊗ s)
--
--CMᵗ : ∀ {s : S l} → Reshape (transp s) s
--CMᵗ {.zz} {ν x} = eq
--CMᵗ {.(ss _)} {ι s} = eq
--CMᵗ {.(ss _)} {s₁ ⊗ s₂} = CM ∙ (CMᵗ ⊕ CMᵗ)

thm₁ : ∀ {dft : {s : S l} → Ar s ℂ → Ar s ℂ}
     → ∀ {twid : ∀ {s p : S (ss l)} → P s → P p → ℂ}
     → ∀ {s : S (ss l)} 
     → ∀ (xs : Ar s ℂ)
     → ∀ (i : P s)
     → cmfft dft twid CM {s} xs i ≡ reshape CMᵗ (fft dft twid {s} xs) i
thm₁ {_} {_} {_} {ι _} _ (ι _) = refl
thm₁ {zz} {dft₁} {twid} {s₁ ⊗ s₂} xs (i₁ ⊗ i₂) = ?
thm₁ {ss l} {dft₁} {twid} {s₁ ⊗ s₂} xs (i₁ ⊗ i₂) = ?
  --  cong ((flip unnest) (((i₁ ⊗ i₂) ⟨ CM ⟩) ⟨ swap ⟩)) ?
  --⊡ ?


remQuot-splits-proof : ∀ {X : Set}
                    → ∀ {s p : S (ss l)}
                    → ∀ {xs ys : Ar (s ⊗ p) X}
                    → ∀ (prf : ∀ (i : P s) (j : P p) → xs (i ⊗ j) ≡ ys (i ⊗ j))
                    → ∀ (i : P (s ⊗ p)) → xs i ≡ ys i
remQuot-splits-proof prf (i₁ ⊗ i₂) = prf i₁ i₂

proj₁-remQuot-⊕ : ∀ {l₁ : L} {s₁ s₂ : S (ss l₁)}
                → ∀ {l₂ : L} {p₁ p₂ : S (ss l₂)}
                → ∀ (i : P (s₁ ⊗ s₂))
                → ∀ (r₁ : Reshape p₁ s₁)
                → ∀ (r₂ : Reshape p₂ s₂)
                → proj₁ (⊗-remQuot p₂ (i ⟨ r₁ ⊕ r₂ ⟩)) ≡ (proj₁ (⊗-remQuot s₂ i)) ⟨ r₁ ⟩ 
proj₁-remQuot-⊕ (i₁ ⊗ i₂) r₁ r₂ = refl

proj₂-remQuot-⊕ : ∀ {l₁ : L} {s₁ s₂ : S (ss l₁)}
                → ∀ {l₂ : L} {p₁ p₂ : S (ss l₂)}
                → ∀ (i : P (s₁ ⊗ s₂))
                → ∀ (r₁ : Reshape p₁ s₁)
                → ∀ (r₂ : Reshape p₂ s₂)
                → proj₂ (⊗-remQuot p₂ (i ⟨ r₁ ⊕ r₂ ⟩)) ≡ (proj₂ (⊗-remQuot s₂ i)) ⟨ r₂ ⟩ 
proj₂-remQuot-⊕ (i₁ ⊗ i₂) _ _ = refl

cong-proj₁-remQuot : ∀ {s p : S (ss l)}
                   → ∀ {i j : P (s ⊗ p)} 
                   → (prf : i ≡ j)
                   → proj₁ (⊗-remQuot p i) ≡ proj₁ (⊗-remQuot p j)

helper₁ : {s₁ s₂ : S (ss (ss l))}
          {xs : Ar (s₁ ⊗ s₂) ℂ} {i₁ : P s₁} {i₂ : P s₂} →
          (proj₁ (⊗-remQuot s₁ ((i₁ ⊗ i₂) ⟨ CM ⟩)) ⟨ rev flatten-zᵣ ⟩) ≡
          proj₁
          (⊗-remQuot (flatten-z s₁)
           (((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩))
helper₁ {l} {s₁} {s₂} {xs} {i₁} {i₂} = 
      ? --sym (proj₁-remQuot-⊕ ((i₁ ⊗ i₂) ⟨ (rev flatten-zᵣ ⊕ rev flatten-zᵣ) ∙ CM ⟩) ? ?)
    ⊡ ?

lemma₃ : ∀ {s₁ s₂ : S (ss (ss l))}
       → ∀ (i₁ : P s₁)
       → ∀ (i₂ : P s₂)
       →  ((((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩) ⟨ (flatten-zᵣ {_} {s₂}) ⊕ (flatten-zᵣ {_} {s₁}) ⟩) ⟨ rev flatten-zᵣ ⟩
        ≡
          ((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩
lemma₃ {l} {s₁} {s₂} i₁ i₂ =
    begin
     ((((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩) ⟨ (flatten-zᵣ {_} {s₂}) ⊕ (flatten-zᵣ {_} {s₁}) ⟩) ⟨ rev flatten-zᵣ ⟩
    ≡⟨⟩
     (i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ⊕ rev flatten-zᵣ ∙ CM ∙ (flatten-zᵣ {_} {s₂}) ⊕ (flatten-zᵣ {_} {s₁}) ∙ rev flatten-zᵣ ⟩
    ≡⟨⟩
     (i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ⊕ rev flatten-zᵣ ∙ CM ∙ (flatten-zᵣ {_} {s₂}) ⊕ (flatten-zᵣ {_} {s₁}) ∙ (rev flatten-zᵣ ⊕ rev flatten-zᵣ) ⟩
    ≡⟨ rev-eq (_⊕_ {_} {_} {s₂} {s₁} flatten-zᵣ flatten-zᵣ) ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ⊕ rev flatten-zᵣ ∙ CM ⟩)  ⟩
     ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ⊕ rev flatten-zᵣ ⟩) ⟨ CM ⟩
    ≡⟨⟩
     ((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩
    ∎

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

thm₂ : ∀ {s : S (ss (ss l))}
     → ∀ {dft : {s : S l} → Ar s ℂ → Ar s ℂ}
     → ∀ {twid : ∀ {r : L} → ∀ {s p : S r} → P s → P p → ℂ}
     → ∀ {dft-cong : ∀ {p : S l} → (a b : Ar p ℂ) → (prf : ∀ i → a i ≡ b i) → ∀ i → dft a i ≡ dft b i}
     --→ ∀ {twid-thm : ∀ {r : L} → ∀ {s : S (ss r)} → ∀ {p : S r} → ∀ (i : P s) → ∀ (j : P p) → twid i j ≡ twid (i ⟨ flattenᵣ ⟩) j} 
     → ∀ (xs : Ar s ℂ)
     → ∀ (i : P s)
     → cmfft {ss l} (cmfft dft twid CM) twid CM {s} xs i ≡ cmfft {l} dft twid CM {flatten-z s} (reshape flatten-zᵣ xs) (i ⟨ rev flatten-zᵣ ⟩)
thm₂ {l} {ι s} {dft₁} {twid} xs (ι i) = refl
thm₂ {l} {s₁ ⊗ s₂} {dft₁} {twid} {dft₁-cong} xs i@(i₁ ⊗ i₂) = 
    remQuot-splits-proof 
        {xs = unnest (λ i₃ →
               cmfft (cmfft dft₁ twid CM) twid
               (λ {s} {p} →
                  (rev flatten-zᵣ ⊕ rev flatten-zᵣ) ∙ CM ∙ (flatten-zᵣ ⊕ flatten-zᵣ))
               (λ j →
                  twid j i₃ *
                  cmfft (cmfft dft₁ twid CM) twid
                  (λ {s} {p} →
                     (rev flatten-zᵣ ⊕ rev flatten-zᵣ) ∙ CM ∙ (flatten-zᵣ ⊕ flatten-zᵣ))
                  (λ j₁ → xs (j₁ ⊗ j)) i₃))
        } 
        {unnest _} 
        (λ j₁ j₂ → 
            thm₂ {_} {_} {_} {twid} {dft₁-cong} _ j₂
          ⊡ cmfft-cong CM dft₁-cong _ _ (λ k₁ → 
              cong₂ _*_
                refl
                (thm₂ {_} {s₁} {_} {twid} {dft₁-cong} _ j₁)
            ) (j₂ ⟨ rev flatten-zᵣ ⟩)
        ) 
        (((((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩) ⟨ flatten-zᵣ ⊕ flatten-zᵣ ⟩) ⟨ swap ⟩)
  ⊡ (
      begin
        unnest {ss l} 
          (λ α φ → 
            cmfft {l} dft₁ twid CM 
              (λ β → 
                  twid {ss (ss l)} (β ⟨ flatten-zᵣ ⟩) α
                * 
                  cmfft {l} dft₁ twid CM 
                  ((λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))))
                  (α ⟨ rev flatten-zᵣ ⟩)
              ) 
              (φ ⟨ rev flatten-zᵣ ⟩)) 
            ((i₁ ⊗ i₂)  
                ⟨ rev flatten-zᵣ ⊕ rev flatten-zᵣ
                ∙ CM 
                ∙ flatten-zᵣ ⊕ flatten-zᵣ
                ∙ swap ⟩)
      ≡⟨ (cong (unnest {ss l} _) (sym (cong (_⟨ swap ⟩) (⊗-combine-remQuot s₁ ((i₁ ⊗ i₂)  ⟨ CM ⟩))))) ⟩
      _ ≡⟨ cmfft-icong {l} {flatten-z s₂} {_} {twid} _ _ (proj₁ (⊗-remQuot (flatten-z s₁) (((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩))) (helper₁ {_} {_} {_} {xs} {_} {i₂}) ⟩ 
      _ ≡⟨ cmfft-cong CM dft₁-cong {flatten-z s₂} _ _ 
            (λ β → 
              cong₂ 
                _*_ 
                ? -- Pretty reasonable property for twid onces revEQ is applied
                (cmfft-icong {twid = twid} (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) _ _ ( 
                    --( cong 
                    --      (_⟨ rev (flatten-zᵣ {ss l} {s₁}) ⟩) 
                    --      (proj₂-remQuot-⊕ (((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩) flatten-zᵣ flatten-zᵣ)
                    --) ⊡ ( cong
                    --        (_⟨ rev (flatten-zᵣ {ss l} {s₁}) ⟩) 
                    --        (sym (proj₂-remQuot-⊕ (((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩) flatten-zᵣ flatten-zᵣ))
                    --) ⊡
                         ( sym ( proj₂-remQuot-⊕ ((((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩) ⟨
               flatten-zᵣ ⊕ flatten-zᵣ ⟩) (rev flatten-zᵣ) (rev flatten-zᵣ) )
                    )
                  )
                )
            ) 
            _ 
         ⟩
         -- Reveq
      _ ≡⟨ cmfft-icong {l} {flatten-z s₂} {_} {twid} _ 
              (proj₁ (⊗-remQuot (flatten-z s₁) (((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩)))
              _ 
              (   sym (rev-eq {_} {_} {s₂} flatten-zᵣ _)
                ⊡ sym (proj₁-remQuot-⊕ (((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩) ((flatten-zᵣ {_} {s₂}) ∙ rev flatten-zᵣ) ((flatten-zᵣ {_} {s₁}) ∙ rev flatten-zᵣ))
                ⊡ (cong-proj₁-remQuot 
                      {_} {_} {_} 
                      {((((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩) ⟨ (flatten-zᵣ ∙ rev flatten-zᵣ) ⊕ (flatten-zᵣ ∙ rev flatten-zᵣ) ⟩)} 
                      {(((((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩) ⟨ flatten-zᵣ ⊕ flatten-zᵣ ⟩) ⟨ rev flatten-zᵣ ⊕ rev flatten-zᵣ ⟩)} 
                      (sym (⊕-distributes-∙ {_} {_} {_} {_} {_} {s₂} flatten-zᵣ {s₁} flatten-zᵣ (rev flatten-zᵣ) (rev flatten-zᵣ) (((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩) ))
                  ) 
              ) 
          ⟩
      _ ≡⟨ (cong (unnest {l} _) ((cong (_⟨ swap ⟩) (⊗-combine-remQuot (flatten-z s₁) (((((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩) ⟨ flatten-zᵣ ⊕ flatten-zᵣ ⟩) ⟨ rev flatten-zᵣ ⊕ rev flatten-zᵣ ⟩))))) ⟩
      _ ≡⟨ cong (unnest {l} _) (cong (_⟨ swap ⟩) ((lemma₃ i₁ i₂))) ⟩
        unnest {l}
          (λ α φ → 
            cmfft {l} dft₁ twid CM 
              (λ β → 
                  twid {ss l} β α
                * 
                  cmfft {l} dft₁ twid CM 
                  (λ δ → xs ((δ ⟨ flatten-zᵣ ⟩) ⊗ (β ⟨ flatten-zᵣ ⟩))) 
                  α
              )
              φ
          ) 
          ((i₁ ⊗ i₂) 
              ⟨ rev flatten-zᵣ ⊕ rev flatten-zᵣ 
              ∙ CM 
              ∙ swap ⟩)
      ≡⟨⟩
        cmfft {l} dft₁ twid CM (reshape flatten-zᵣ xs) ((i₁ ⊗ i₂) ⟨ rev flatten-zᵣ ⟩)
      ∎
    )

--with ⊗-remQuot _ (((i₁ ⟨ rev flatten-zᵣ ⟩) ⊗ (i₂ ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩)
--... | fst , snd = ?
  --ext-cong-app ? ?
--tma {_} {_} {?} {?} {?} ? ?
  --  remove-reshape {_} {_} {_} {_} {?} {?} {CMᵗ} ? i
  --⊡ ?




















----------------------------------

map-flat : S (ss (ss l)) → S (ss (ss l))
map-flat (ι x) = ι (ι (flatten-z x))
map-flat (s ⊗ p) = map-flat s ⊗ map-flat p

map-flatᵣ : ∀ {s : S (ss (ss l))} → Reshape s (map-flat s)
map-flatᵣ {l} {ι s} = up (up (down flatten-zᵣ))
map-flatᵣ {l} {s ⊗ p} = map-flatᵣ ⊕ map-flatᵣ


module X (l : L) (Pred : S l → Set) where
  data All : S (ss l) → Set where
    ι : ∀ {s : S l} → Pred s → All (ι s)
    _⊗_ : ∀ {s p : S (ss l)} → All s → All p → All (s ⊗ p)


  fftx : (dft : {s : S l} → Ar s ℂ → Ar s ℂ)
       → (twid : ∀ {s p : S (ss l)} → P s → P p → ℂ)
       → {s : S (ss l)} → All s → Ar s ℂ → Ar (transp s) ℂ
  fftx dft twid {ι s} _ a = reshape (up eq) (dft (reshape (down eq) a))
  fftx dft twid {s ⊗ p} (all₁ ⊗ all₂) a = 
    let 
      b = map (fftx dft twid all₁) (nest (reshape swap a))
      c = unnest (λ i → zipWith _*_ (twid i) (b i)) 
      d = map (fftx dft twid all₂) (nest (reshape swap c))
    in reshape swap (unnest d)

  fftx-cong : ∀ {dft : {s : S l} → Ar s ℂ → Ar s ℂ}
       → {twid : ∀ {s p : S (ss l)} → P s → P p → ℂ}
       → {s : S (ss l)} 
       → (all : All s) 
       → (xs ys : Ar s ℂ)
       → (prf : ∀ i → xs i ≡ ys i)
       → ∀ i → fftx dft twid all xs i ≡ fftx dft twid all ys i
       
open X

data ι-flat : S (ss l) → Set where
  ι : (s : S l)→ ι-flat (ι s)

map-flat⇒All-ι-flat : ∀ {s : S (ss (ss l))} → Σ (S (ss (ss l))) (λ s′ → All (ss l) ι-flat s′)
proj₁ (map-flat⇒All-ι-flat {l} {s}) = map-flat s
proj₂ (map-flat⇒All-ι-flat {l} {ι s}) = ι (ι (flatten-z s))
proj₂ (map-flat⇒All-ι-flat {l} {s ⊗ p}) = (map-flat⇒All-ι-flat .proj₂) ⊗ (map-flat⇒All-ι-flat .proj₂)

open import Data.Unit

all-⊤ : ∀ {s : S (ss l)} → All l (λ _ → ⊤) s
all-⊤ {l} {ι s} = ι tt
all-⊤ {l} {s ⊗ s₁} = all-⊤ ⊗ all-⊤



lower-all-s : ∀ {s : S (ss (ss l))} → All (ss l) ι-flat s → S (ss l)
lower-all-s {l} {ι s} (ι x) = s
lower-all-s {l} {s ⊗ s₁} (x₁ ⊗ x₂) = lower-all-s x₁ ⊗ lower-all-s x₂

lower-all-p : ∀ {s : S (ss (ss l))} → (all : All (ss l) ι-flat s) → P (s) → P (lower-all-s all)
lower-all-p (ι x) (ι x₁) = x₁
lower-all-p (all ⊗ all₁) (x ⊗ x₁) = lower-all-p all x ⊗ lower-all-p all₁ x₁

raise-all-p : ∀ {s : S (ss (ss l))} → (all : All (ss l) ι-flat s) → P (lower-all-s all) → P s
raise-all-p (ι x) (ι x₁) = ι (ι x₁)
raise-all-p (all ⊗ all₁) (x ⊗ x₁) = (raise-all-p all x) ⊗ (raise-all-p all₁ x₁)
lower-all-Ar : ∀ {X : Set} → ∀ {s : S (ss (ss l))} → (all : All (ss l) ι-flat s) → Ar s X → Ar (lower-all-s all) X
lower-all-Ar all xs i = xs (raise-all-p all i)

p-transp-lower : ∀ {s : S (ss (ss l))} → (all : All (ss l) ι-flat s) →  P (transp s) → P (transp (lower-all-s all))
p-transp-lower (ι x) (ι x₁) = x₁ ⟨ transpᵣ ⟩ 
p-transp-lower (all ⊗ all₁) (x ⊗ x₁) = p-transp-lower all₁ x ⊗ p-transp-lower all x₁

lemma₂ : ∀ {l : L} 
      → {s : S (ss (ss l))}
      → ∀ (dft₁ : {s : S l} → Ar s ℂ → Ar s ℂ)
      → ∀ (dft-cong : ∀ {p : S l} → {a b : Ar p ℂ} → ∀ i → dft₁ a i ≡ dft₁ b i )
      → ∀ (twid : ∀ {lv : L} → ∀ {s p : S (ss lv)} → P s → P p → ℂ)
      → ∀ (xs : Ar s ℂ)
      → ∀ (i : P s)
      → cmfft {l} dft₁ twid CM
            {lower-all-s (map-flat⇒All-ι-flat {l} {s} .proj₂)} 
            (λ i₁ → xs ((raise-all-p (map-flat⇒All-ι-flat .proj₂) i₁) ⟨ map-flatᵣ ⟩)) 
            (lower-all-p (map-flat⇒All-ι-flat {l} {s} .proj₂) (i ⟨ rev map-flatᵣ ⟩)) 
      ≡
        cmfft {l} dft₁ twid CM
            {flatten s} 
            (λ i₁ → xs (i₁ ⟨ flattenᵣ ⟩)) 
            ((i ⟨ rev flattenᵣ ⟩))
  -- This case is simply cmfft≡dft for level l which should be okay
lemma₂ {l} {ι s} dft₁ dft-cong₁ twid xs i = ?
lemma₂ {l} {s ⊗ s₁} dft₁ dft-cong₁ twid xs i = ?

































































{-
-- Kind of a basic sanity check before moving onto bigger
    -- Which has been useful - because I currently can only make proofs upon one level
    -- and proof against the DFT for (xs ∈ ss zz)..
dft≡post-ufft : ∀ {s : S (ss l)}
         → ∀ (xs : Ar s ℂ)
         → ∀ (i : P s)
         → (reshape (rev ν-flattenᵣ) ∘ dft ∘ reshape  ν-flattenᵣ) xs i 
         ≡ reshape 
              (change-majorᵣ ∙ (rev transpᵣ)) 
              (post-ufft (reshape (rev ν-flattenᵣ) ∘ dft ∘ reshape  ν-flattenᵣ) (λ j₁ j₂ → twiddles j₁ (j₂ ⟨ transpᵣ ⟩)) xs) 
              i
dft≡post-ufft {l} {ι s} xs (ι i) = 
  cong (dft (λ i₁ → xs (ι (i₁ ⟨ ν-flattenᵣ ⟩)))) ? --( sym (single-level {?} {?} ?) ⊡ ?)
  ⊡ sym (post-ufft≡fft {l} {reshape (rev ν-flattenᵣ) ∘ dft ∘ reshape  ν-flattenᵣ} {twiddles} ? xs ((ι i) ⟨ change-majorᵣ ⟩))
dft≡post-ufft {l} {s ⊗ s₁} xs i = ?

module X (l : L) (Pred : S l → Set) where
  data All : S (ss l) → Set where
    ι : ∀ {s : S l} → Pred s → All (ι s)
    _⊗_ : ∀ {s p : S (ss l)} → All s → All p → All (s ⊗ p)


  fftx : (dft : {s : S l} → Ar s ℂ → Ar s ℂ)
       → (twid : ∀ {s p : S (ss l)} → P s → P p → ℂ)
       → {s : S (ss l)} → All s → Ar s ℂ → Ar (transp s) ℂ
  fftx dft twid {ι s} _ a = reshape (up eq) (dft (reshape (down eq) a))
  fftx dft twid {s ⊗ p} (all₁ ⊗ all₂) a = 
    let 
      b = map (fftx dft twid all₁) (nest (reshape swap a))
      c = unnest (λ i → zipWith _*_ (twid i) (b i)) 
      d = map (fftx dft twid all₂) (nest (reshape swap c))
    in reshape swap (unnest d)

  fftx-cong : ∀ {dft : {s : S l} → Ar s ℂ → Ar s ℂ}
       → {twid : ∀ {s p : S (ss l)} → P s → P p → ℂ}
       → {s : S (ss l)} 
       → (all : All s) 
       → (xs ys : Ar s ℂ)
       → (prf : ∀ i → xs i ≡ ys i)
       → ∀ i → fftx dft twid all xs i ≡ fftx dft twid all ys i





--fft₁≡fft₂ {l} {ι s} dft₁ twid xs (ι i) = ? -- Trivial as changemajor doesn't effect ι
--fft₁≡fft₂ {l} {s₁ ⊗ s₂} dft₁ twid xs (i₁ ⊗ i₂) = ?

StripSzz : S zz → U
StripSzz (ν x) = x

StripSzz-id : ∀ {s : S zz} → Reshape s (ν (StripSzz s))
StripSzz-id {ν x} = eq

flatten-z : S (ss l) → S l
flatten-z {l} (ι x) = x
flatten-z {zz} (x ⊗ y) = ν (StripSzz (flatten-z x) ● StripSzz (flatten-z y))
flatten-z {ss l} (x ⊗ y) = (flatten-z x) ⊗ (flatten-z y)

flatten-zᵣ : ∀ {s : S (ss l)} → Reshape s (flatten-z s)
flatten-zᵣ {l} {ι s} = down eq
flatten-zᵣ {zz} {s ⊗ s₁} = flat ∙ ((up StripSzz-id ∙ flatten-zᵣ) ⊕ (up StripSzz-id ∙ flatten-zᵣ))
flatten-zᵣ {ss l} {s ⊗ s₁} = flatten-zᵣ ⊕ flatten-zᵣ

map-flat : S (ss (ss l)) → S (ss (ss l))
map-flat (ι x) = ι (ι (flatten-z x))
map-flat (s ⊗ p) = map-flat s ⊗ map-flat p

open import Data.Product
  
map-flatᵣ : ∀ {s : S (ss (ss l))} → Reshape s (map-flat s)
map-flatᵣ {l} {ι s} = up (up (down flatten-zᵣ))
map-flatᵣ {l} {s ⊗ p} = map-flatᵣ ⊕ map-flatᵣ


open X
    
data ι-flat : S (ss l) → Set where
  ι : (s : S l)→ ι-flat (ι s)

map-flat⇒All-ι-flat : ∀ {s : S (ss (ss l))} → Σ (S (ss (ss l))) (λ s′ → All (ss l) ι-flat s′)
proj₁ (map-flat⇒All-ι-flat {l} {s}) = map-flat s
proj₂ (map-flat⇒All-ι-flat {l} {ι s}) = ι (ι (flatten-z s))
proj₂ (map-flat⇒All-ι-flat {l} {s ⊗ p}) = (map-flat⇒All-ι-flat .proj₂) ⊗ (map-flat⇒All-ι-flat .proj₂)

open import Data.Unit

all-⊤ : ∀ {s : S (ss l)} → All l (λ _ → ⊤) s
all-⊤ {l} {ι s} = ι tt
all-⊤ {l} {s ⊗ s₁} = all-⊤ ⊗ all-⊤


fft₂≡fftx₂ : ∀ {s : S (ss (ss l))}
           → ∀ (dft : {s : S l} → Ar s ℂ → Ar s ℂ)
           → ∀ (twid : ∀ {lv : L} → ∀ {s p : S (ss lv)} → P s → P p → ℂ)
           → ∀ (xs : Ar s ℂ)
           → ∀ (i : P s)
           → 
  fft {ss l} (reshape change-majorᵣ ∘ (fft {l} dft twid)) twid {s} xs (i ⟨ change-majorᵣ ⟩)
  ≡
  fftx (ss l) (λ _ → ⊤) (reshape change-majorᵣ ∘ (fft {l} dft twid)) twid all-⊤ xs (i ⟨ change-majorᵣ ⟩)

-- This gives me bad vibes...
map-flat-transp : ∀ {s : S (ss (ss l))} → Reshape (transp s) (transp (map-flat s))
map-flat-transp {l} {s} = ? --(rev change-majorᵣ) ∙  (map-flatᵣ ∙ change-majorᵣ)
--map-flat-transp {l} {ι s   } = map-flatᵣ
--map-flat-transp {l} {s ⊗ s₁} = map-flat-transp {l} {s₁} ⊕ map-flat-transp {l} {s}

fftx₂≡fftx₂∘♭ : ∀ {s : S (ss (ss l))}
              → ∀ (ft : {p : S (ss l)} → Ar p ℂ → Ar p ℂ)
              → (prop₁ : ∀ {p : S (ss l)} (ys : Ar (ι p) ℂ) → ∀ i 
                → ft (reshape (down eq) ys) i 
                    ≡ reshape (down (rev flatten-zᵣ)) (ft (reshape (up (down flatten-zᵣ)) ys)) i)
                    --≡ reshape (down (rev flatten-zᵣ)) (ft (reshape (up (down flatten-zᵣ)) ys)) i)
              → ∀ (twid : ∀ {lv : L} → ∀ {s p : S (ss lv)} → P s → P p → ℂ)
              → ∀ (xs : Ar s ℂ)
              → ∀ (i : P (transp s))
              → 
  fftx (ss l) (λ _ → ⊤) ft twid all-⊤ xs i
  ≡ 
  fftx (ss l) ι-flat ft twid 
      (map-flat⇒All-ι-flat .proj₂) (reshape map-flatᵣ xs) (i ⟨ rev map-flat-transp ⟩)
fftx₂≡fftx₂∘♭ {l} {ι s} ft₁ prop₁ twid xs (ι i) = 
  begin
    ft₁ {s} (λ i₁ → xs (ι i₁)) i
  ≡⟨⟩
    ft₁ {s} (reshape (down eq) xs) i
  ≡⟨ ? ⟩
  --≡⟨ prop₁ {_} xs i ⟩
    ft₁ {ι (flatten-z s)} (reshape (up (down flatten-zᵣ)) xs) ((i ⟨ down (rev flatten-zᵣ) ⟩))
  ≡⟨⟩
    ft₁ {ι (flatten-z s)} (λ k → xs (k ⟨ up (down flatten-zᵣ) ⟩)) (ι (i ⟨ rev flatten-zᵣ ⟩))
  ∎
fftx₂≡fftx₂∘♭ {l} {s ⊗ p} ft₁ prop₁ twid xs (i ⊗ j) =
    fftx₂≡fftx₂∘♭ ft₁ prop₁ twid _ i
  ⊡ fftx-cong (ss l) ι-flat (map-flat⇒All-ι-flat .proj₂) _ _ 
    (λ k →  
      cong₂ 
        _*_ 
        ? -- This is only provable if we know i to be change-majored
        (fftx₂≡fftx₂∘♭ ft₁ prop₁ twid _ j)
    ) 
    (i ⟨ rev map-flat-transp ⟩)

lower-all-s : ∀ {s : S (ss (ss l))} → All (ss l) ι-flat s → S (ss l)
lower-all-s {l} {ι s} (ι x) = s
lower-all-s {l} {s ⊗ s₁} (x₁ ⊗ x₂) = lower-all-s x₁ ⊗ lower-all-s x₂

lower-all-p : ∀ {s : S (ss (ss l))} → (all : All (ss l) ι-flat s) → P (s) → P (lower-all-s all)
lower-all-p (ι x) (ι x₁) = x₁
lower-all-p (all ⊗ all₁) (x ⊗ x₁) = lower-all-p all x ⊗ lower-all-p all₁ x₁

raise-all-p : ∀ {s : S (ss (ss l))} → (all : All (ss l) ι-flat s) → P (lower-all-s all) → P s
raise-all-p (ι x) (ι x₁) = ι (ι x₁)
raise-all-p (all ⊗ all₁) (x ⊗ x₁) = (raise-all-p all x) ⊗ (raise-all-p all₁ x₁)

lower-all-Ar : ∀ {X : Set} → ∀ {s : S (ss (ss l))} → (all : All (ss l) ι-flat s) → Ar s X → Ar (lower-all-s all) X
lower-all-Ar all xs i = xs (raise-all-p all i)

p-transp-lower : ∀ {s : S (ss (ss l))} → (all : All (ss l) ι-flat s) →  P (transp s) → P (transp (lower-all-s all))
p-transp-lower (ι x) (ι x₁) = x₁ ⟨ transpᵣ ⟩ 
p-transp-lower (all ⊗ all₁) (x ⊗ x₁) = p-transp-lower all₁ x ⊗ p-transp-lower all x₁

fftx₂∘♭≡fftx₁ : ∀ {s : S (ss (ss l))}
              → (all : All (ss l) ι-flat s)
              → ∀ (ft : {p : S (ss l)} → Ar p ℂ → Ar p ℂ)
              → ∀ (twid : ∀ {lv : L} → ∀ {s p : S (ss lv)} → P s → P p → ℂ)
              → ∀ (xs : Ar s ℂ)
              → ∀ (i : P (transp s))
              → 
  fftx (ss l) ι-flat ft twid all xs i
  ≡ 
  fftx l (λ _ → ⊤) (reshape (down eq) ∘ ft ∘ reshape (up eq)) twid {lower-all-s all} all-⊤ (lower-all-Ar all xs) (p-transp-lower all i)


fftx₁≡fft₁ : ∀ {s : S ((ss l))}
              → ∀ (ft : {p : S l} → Ar p ℂ → Ar p ℂ)
              → ∀ (twid : ∀ {lv : L} → ∀ {s p : S (ss lv)} → P s → P p → ℂ)
              → ∀ (xs : Ar s ℂ)
              → ∀ (i : P (transp s))
              → 
    fftx l (λ _ → ⊤) ft twid {s} all-⊤ (xs) (i)
  ≡ fft ft twid xs i 


{-
lemma : ∀ {X : Set} → ∀ {s : S (ss (ss l))} → (xs : Ar (s) X) → ∀ (i : P s)
      → xs (raise-all-p (map-flat⇒All-ι-flat .proj₂) i ⟨ map-flatᵣ ⟩)
        ≡
        xs (i ⟨ flattenᵣ ⟩)
-}


dft-eq-helper : {s : S (ss (ss l))}
                {dft = dft₁ : {s = s₁ : S l} → Ar s₁ ℂ → Ar s₁ ℂ}
                {xs : Ar s ℂ} {i : P s} {s = s₁ : S l} (ys : Ar s₁ ℂ) (j : P s₁) →
                dft₁ (λ i₁ → ys i₁) ((ι j ⟨ change-majorᵣ ⟩) ⟨ up eq ⟩) ≡ dft₁ ys j
dft-eq-helper {dft = dft₁} {s = s₁} ys j rewrite single-level j = refl

-- This cannot be defined without first providing a concrete definition of 
-- change-majorᵣ 
-- Which is why we have to go through flattening !!!!!!!!!!!!!!!!!!!!!!!!!!
fft₁≡fft₂ : ∀ {s : S (ss (ss l))}
          → ∀ (dft : {s : S l} → Ar s ℂ → Ar s ℂ)
          → ∀ (dft-cong : ∀ {p : S l} → {a b : Ar p ℂ} → ∀ i → dft a i ≡ dft b i )
          → ∀ (twid : ∀ {lv : L} → ∀ {s p : S (ss lv)} → P s → P p → ℂ)
          → ∀ (xs : Ar s ℂ)
          → ∀ (i : P s)
          → 
            reshape change-majorᵣ
            ( fft 
                {ss l} 
                (reshape change-majorᵣ ∘ (fft {l} dft twid))
                twid 
                {s}
                xs
            ) i 
            ≡
            reshape (rev flattenᵣ) (reshape change-majorᵣ
            ( fft 
              {l} 
              dft
              twid
              {flatten s} 
              (reshape flattenᵣ xs) 
            )) i
fft₁≡fft₂ {l} {s} dft₁ dft-cong₁ twid xs i =
    fft₂≡fftx₂ dft₁ twid xs i 
  ⊡ fftx₂≡fftx₂∘♭ (reshape change-majorᵣ ∘ (fft {l} dft₁ twid)) ? twid xs (i ⟨ change-majorᵣ ⟩)
  ⊡ fftx₂∘♭≡fftx₁ (map-flat⇒All-ι-flat .proj₂) (reshape change-majorᵣ ∘ (fft {l} dft₁ twid)) twid (reshape map-flatᵣ xs) (i ⟨ change-majorᵣ ∙ rev map-flat-transp ⟩)
  ⊡ fftx₁≡fft₁ (reshape (down eq) ∘ reshape change-majorᵣ ∘ (fft {l} dft₁ twid) ∘ reshape (up eq)) twid ((lower-all-Ar (map-flat⇒All-ι-flat .proj₂) (reshape map-flatᵣ xs))) 
      (p-transp-lower (map-flat⇒All-ι-flat .proj₂) (i ⟨ change-majorᵣ ∙ (rev map-flat-transp) ⟩))
  ⊡ fft-dft-cong 
      (λ {s = s₁} z z₁ → dft₁ (λ i₁ → z i₁) ((ι z₁ ⟨ change-majorᵣ ⟩) ⟨ up eq ⟩)) 
      dft₁ 
      (λ a b prf → dft-cong₁ ) 
      (dft-eq-helper {_} {_} {dft₁} {xs} {i})
      ((lower-all-Ar (map-flat⇒All-ι-flat .proj₂) (reshape map-flatᵣ xs))) 
      (p-transp-lower (map-flat⇒All-ι-flat .proj₂) (i ⟨ change-majorᵣ ∙ (rev map-flat-transp) ⟩))
  ⊡ (begin
        fft {l} dft₁ twid 
            {lower-all-s (map-flat⇒All-ι-flat {l} {s} .proj₂)} 
            (λ i₁ → xs ((raise-all-p (map-flat⇒All-ι-flat .proj₂) i₁) ⟨ map-flatᵣ ⟩)) 
            (p-transp-lower (map-flat⇒All-ι-flat .proj₂) ((i ⟨ change-majorᵣ ⟩) ⟨ rev map-flat-transp ⟩))
      ≡⟨ ? ⟩ 
        fft {l} dft₁ twid 
            {flatten s} 
            (λ i₁ → xs (i₁ ⟨ flattenᵣ ⟩)) 
            ((i ⟨ rev flattenᵣ ⟩) ⟨ change-majorᵣ ⟩)
      ∎)

lemma : {s : S (ss (ss l))}
        {dft = dft₁ : {s = s₁ : S l} → Ar s₁ ℂ → Ar s₁ ℂ}
        {dft-cong = dft-cong₁
         : {p : S l} {a b : Ar p ℂ} (i : P p) → dft₁ a i ≡ dft₁ b i}
        {twid
         : {lv : L} {s = s₁ : S (ss lv)} {p : S (ss lv)} → P s₁ → P p → ℂ}
        {xs : Ar s ℂ} {i : P s} →
        fft {l} dft₁ twid 
            {lower-all-s (map-flat⇒All-ι-flat {l} {s} .proj₂)} 
            (λ i₁ → xs ((raise-all-p (map-flat⇒All-ι-flat .proj₂) i₁) ⟨ map-flatᵣ ⟩)) 
            (p-transp-lower (map-flat⇒All-ι-flat .proj₂) ((i ⟨ change-majorᵣ ⟩) ⟨ rev map-flat-transp ⟩))
        ≡
        fft {l} dft₁ twid 
            {flatten s} 
            (λ i₁ → xs (i₁ ⟨ flattenᵣ ⟩)) 
            ((i ⟨ rev flattenᵣ ⟩) ⟨ change-majorᵣ ⟩)

lemma {l} {ι s} {dft = dft₁} {dft-cong = dft-cong₁} {twid} {xs} {ι i} = ?
lemma {l} {s ⊗ s₁} {dft = dft₁} {dft-cong = dft-cong₁} {twid} {xs} {i ⊗ i₁} = ?
-- Not the case of couse - but can I form the above relation is the big question for me right now
tempa : ∀ {s : S (ss (ss l))} → lower-all-s (map-flat⇒All-ι-flat {l} {s} .proj₂) ≡ flatten s
tempa {l} {ι (ι s)} = refl
tempa {l} {ι (s ⊗ s₁)} = ?
tempa {l} {s ⊗ s₁} = ?
{-
-- This is too general ∀ r, but may be possible to define as a propertie of CM
remove-cm : ∀ {s : S (ss l)}
   → ∀ {dft : {s : S l} → Ar s ℂ → Ar s ℂ}
   → ∀ {twid : ∀ {lv : L} → ∀ {s p : S (ss lv)} → P s → P p → ℂ}
   → ∀ (r : Reshape {ss l} {ss l} (transp s) s)
   → (xs : Ar s ℂ)
   → (i : P s)
   → fft {l} dft twid {s} xs (i ⟨ transpᵣ ⟩)
   ≡ fft {l} dft twid {s} xs (i ⟨ r ⟩)
remove-cm {s = ι s} eq xs (ι i) = refl
remove-cm {s = ι s} (r ∙ r₁) xs (ι i) = ?
remove-cm {s = ι s} (up r) xs (ι i) = ?
remove-cm {s = ι s} (down r) xs (ι i) = ?
remove-cm {s = s₁ ⊗ s₂} r xs (i₁ ⊗ i₂) = ?
-}

{-
tmp₂ : ∀ {X : Set} → 
    → ∀ {l o : L} {s : S l} {p : S o} 
    → ∀ (xs ys : Ar s X) 
    → ∀ (r : Reshape {l} {o} s p)
    → ∀ (prf : ∀ (i : P s) → xs i ≡ ys i)
    → ∀ (i : P p) → xs (i ⟨ r ⟩) ≡ ys (i ⟨ r ⟩)
tmp₂ xs ys r prf i = ?
-}


--map-flat-Σ : ∀ {s : S (ss (ss l))} → Σ (S (ss (ss l))) (λ i → ?)

                    -- Interesting effect of up/ down - (up ≢ rev down)?
--map-flatᵣ {l} {ι s} = up (up (down flattenᵣ)) 
--                    --up (down (up flattenᵣ)) 
--                    --down (up (up flattenᵣ))
--map-flatᵣ {l} {s ⊗ s₁} = map-flatᵣ ⊕ map-flatᵣ
--map-flatᵣ {_} {ι s} = eq 
--map-flatᵣ {_} {s ⊗ s₁} = up (flattenᵣ ⊕ flattenᵣ)



lemma₁ : ∀ {s : S (ss (ss l))}
          → ∀ (dft : {s : S l} → Ar s ℂ → Ar s ℂ)
          → ∀ (twid : ∀ {lv : L} → ∀ {s p : S (ss lv)} → P s → P p → ℂ)
          → ∀ (xs : Ar s ℂ)
          → ∀ (i : P s) 
          → fft 
              {ss l} 
              (reshape change-majorᵣ ∘ (fft {l} dft twid))
              twid 
              {s} 
              xs
              (i ⟨ change-majorᵣ ⟩)
          ≡ fft 
              {ss l} 
              (reshape change-majorᵣ ∘ (fft {l} dft twid))
              twid 
              {map-flat s} 
              (reshape map-flatᵣ xs)
              (i ⟨ (rev map-flatᵣ) ∙ change-majorᵣ ⟩)
lemma₁ {l} {s} dft₁ twid xs i = ?

--lemma₁ {l} {ι s} dft₁ twid xs i = refl
--lemma₁ {l} {s ⊗ s₁} dft₁ twid xs i = ?




--     CM (fft {ss l} (CM ∘ fft {l}) xs)
-- ≡⟨⟩ CM (fft {ss l} (CM ∘ fft {l}) (map-flat xs))
-- ≡⟨⟩ ?
-- ≡⟨⟩ ?
-- ≡⟨⟩ ?
-- ≡⟨⟩ ?
-- ≡⟨⟩ ?
-- ≡⟨⟩ ?
-- ≡⟨⟩ ?
-- ≡⟨⟩ ?
-- ≡⟨⟩ ?
-- ≡⟨⟩ unflatten (CM ( fft {l} dft (flatten  xs)))



















{-
fft₁≡fft₂ : ∀ {s : S (ss (ss l))}
          → (dft : {s : S (ss l)} → Ar s ℂ → Ar s ℂ)
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
          ≡ ? {-fft 
              {ss l} 
              dft 
              twid 
              {s} 
              xs 
              (i ⟨ change-majorᵣ ⟩)
              -}
              -}








{-
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
-}
-}

