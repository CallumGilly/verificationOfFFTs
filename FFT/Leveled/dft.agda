{-# OPTIONS --allow-unsolved-metas #-}
open import ComplexNew

module FFT.Leveled.dft (cplx : Cplx) where


open Cplx cplx
open import Matrix.Mon
open import Matrix.NatMon
open import Matrix.Leveled.Base ℕ-Mon
open import Matrix.Leveled.Reshape ℕ-Mon
open import Matrix.Leveled.Change-Major ℕ-Mon
open import Matrix.Leveled.NatMon-Sum cplx
open import Matrix.Leveled.NatMon-Change-Major
open Mon ℕ-Mon
open import FFT.Leveled.Specification cplx ℕ-Mon ℕ-CM
open import FFT.Leveled.FFT cplx ℕ-Mon
open Change-Major ℕ-CM

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning

open import Data.Fin hiding (_+_; pred)
open import Data.Nat renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties

private
  variable
    ℓ ℓ′ : L
    n : U
    X : Set

  infixl 4 _⊡_
  _⊡_ = trans

-- Be careful here, given i : Fin ∘ suc
--iota : ∀ {n : U} → Ar (ι (ν n)) ℕ
--iota (ι (ν x)) = toℕ x

ℕ-twiddles : ∀ {s p : S (ss ℓ)} → ℕ → P s → P p → ℂ
ℕ-twiddles {l} {s} {p} n i j = -ω (n) ((iota (i ⟨ rev (up ν-flattenᵣ) ⟩)) *ₙ (iota (j ⟨ rev (up ν-flattenᵣ) ⟩)))


length-transp : ∀ (s : S ℓ) → length s ≡ length (transp s)
length-transp s = resh-length {_} {_} {s} (rev transpᵣ)

module ℕ-dft′ where
  dft : ∀ {s : S zz} 
        → Ar s ℂ 
        → Ar s ℂ
  dft {ν n} xs j = sum (λ k → xs k * ℕ-twiddles n (ι k) (ι j))

  dft-cong : ∀ {s : S zz} (xs ys : Ar s ℂ) →
             ((i : P s) → xs i ≡ ys i) → (i : P s) → dft xs i ≡ dft ys i
  dft-cong {ν n} xs ys prf (ν j) = sum-cong 
                                    {n} 
                                    {(λ k → xs k * -ω _ (iota (P.ι k) *ₙ toℕ j))} 
                                    {(λ k → ys k * -ω _ (iota (P.ι k) *ₙ toℕ j))} 
                                    λ{ (ν i) → 
                                      cong₂ _*_ (prf (ν i)) refl
                                    }

  twiddles : ∀ {s p : S (ss ℓ)} → P s → P p → ℂ
  twiddles {_} {s} {p} i j = ℕ-twiddles ((length s *ₙ length p +ₙ length s +ₙ length p)) i j

  open import Matrix.Leveled.IotaHelper ℕ-Mon

  CM-isInplace : ∀ {s p : S (ss ℓ)} → InplaceReshape (CM {_} {s} {p})
  CM-isInplace {zz} {s} {p} = (Inplace-rev _ flatten-z-isInplace) ∙ ({-subst InplaceReshape ? -} ?) ∙ flatten-z-isInplace
  CM-isInplace {ss ℓ} {s} {p} = (Inplace-rev _ flatten-z-isInplace) ⊕ (Inplace-rev _ flatten-z-isInplace) ∙ CM-isInplace ∙ flatten-z-isInplace ⊕ flatten-z-isInplace

  CMᵗ-isInplace : ∀ {s : S ℓ} → InplaceReshape (CMᵗ {_} {s})
  CMᵗ-isInplace {zz} {ν x} = eq
  CMᵗ-isInplace {ss ℓ} {ι s} = eq
  CMᵗ-isInplace {ss ℓ} {s₁ ⊗ s₂} = CMᵗ-isInplace ⊕ CMᵗ-isInplace ∙ CM-isInplace

  open import Function

  twiddles-CMᵗᵣ-lemma : ∀ {s p : S (ss ℓ)}
                      → ∀ (i : P s) 
                      → ∀ (j : P p) 
                      → twiddles i (j ⟨ CMᵗ ⟩) ≡ twiddles i j
  twiddles-CMᵗᵣ-lemma {ℓ} {s} {.(S.ι _)} i (ι j) = refl
  twiddles-CMᵗᵣ-lemma {ℓ} {s} {(p₁ ⊗ p₂)} i (j₁ ⊗ j₂) rewrite
      resh-length {s = p₁} (rev transpᵣ)
    | resh-length {s = p₂} (rev transpᵣ)
    | ∘-suc-lemma₂ (length (transp p₁)) (length (transp p₂)) =
      cong₂ -ω 
        refl
        (cong₂ 
          _*ₙ_ 
          {iota′ (i ⟨ rev ν-flattenᵣ ⟩)} 
          {_} 
          {iota′ (((((j₁ ⟨ CMᵗ ⟩) ⊗ (j₂ ⟨ CMᵗ ⟩)) ⟨ CM ⟩) ⟨ down (rev ν-flattenᵣ) ⊕ down (rev ν-flattenᵣ) ⟩) ⟨ unflat ⟩)} 
          {iota′ ((ι (j₁ ⟨ rev ν-flattenᵣ ⟩) ⊗ ι (j₂ ⟨ rev ν-flattenᵣ ⟩)) ⟨ unflat ⟩)} 
          refl
          ?
        )
{-
    iota′ (i ⟨ rev ν-flattenᵣ ⟩) 
  *ₙ 
    iota′ (((((j₁ ⟨ CMᵗ ⟩) ⊗ (j₂ ⟨ CMᵗ ⟩)) ⟨ CM ⟩) ⟨ down (rev ν-flattenᵣ) ⊕ down (rev ν-flattenᵣ) ⟩) ⟨ unflat ⟩) 
≡ 
    iota′ (i ⟨ rev ν-flattenᵣ ⟩) 
  *ₙ 
    iota′ ((ι (j₁ ⟨ rev ν-flattenᵣ ⟩) ⊗ ι (j₂ ⟨ rev ν-flattenᵣ ⟩)) ⟨ unflat ⟩)
-}
  {-
      cong₂ -ω 
        ? --(cong ((length s) *ₙ_) (resh-length {_} {_} {(transp (p₁ ⊗ p₂))} transpᵣ))
        (cong₂ _*ₙ_ {_} {_} {iota (ι (((((j₁ ⟨ CMᵗ ⟩) ⊗ (j₂ ⟨ CMᵗ ⟩)) ⟨ CM ⟩) ⟨ rev (up ν-flattenᵣ) ⊕ rev (up ν-flattenᵣ) ⟩) ⟨ unflat ⟩))} {iota (ι (((j₁ ⟨ rev (up ν-flattenᵣ) ⟩) ⊗ (j₂ ⟨ rev (up ν-flattenᵣ) ⟩)) ⟨ unflat ⟩))} refl 
        ?
        -}
            --(((((j₁ ⟨ CMᵗ ⟩) ⊗ (j₂ ⟨ CMᵗ ⟩)) ⟨ CM ⟩) ⟨ rev u-flattenᵣ ⊕ rev u-flattenᵣ ⟩) ⟨ unflat ⟩)
---(((j₁ ⟨ rev u-flattenᵣ ⟩) ⊗ (j₂ ⟨ rev u-flattenᵣ ⟩)) ⟨ unflat ⟩)
        --)
  --rewrite length-transp p₁ | length-transp p₂ = cong₂ -ω ? ?


  flatten-z₂-preserves-length : ∀ {s p : S (ss (ss ℓ))}
                              → (length (flatten-z s) *ₙ length (flatten-z p) +ₙ length (flatten-z s) +ₙ length (flatten-z p))
                              ≡ length s *ₙ length p +ₙ length s +ₙ length p
  flatten-z₂-preserves-length {ℓ} {s} {p} = sym 
                                              (cong₂ _+ₙ_ 
                                                (cong₂ _+ₙ_ 
                                                  (cong₂ _*ₙ_ 
                                                    (resh-length {_} {_} {s} flatten-zᵣ) 
                                                    (resh-length {_} {_} {p} flatten-zᵣ)
                                                  ) 
                                                  (resh-length {_} {_} {s} flatten-zᵣ)
                                                ) 
                                                (resh-length {_} {_} {p} flatten-zᵣ)
                                              )

  twiddles-flatten-zᵣ-lemma : ∀ {s p : S (ss (ss ℓ))}
                            → ∀ (i : P (flatten-z s))
                            → ∀ (j : P (flatten-z p))
                            → twiddles {_} {s} {p} (i ⟨ flatten-zᵣ ⟩) (j ⟨ flatten-zᵣ ⟩)
                            ≡ twiddles i j
  twiddles-flatten-zᵣ-lemma {ℓ} {s} {p} i j = cong₂ -ω 
        (sym (flatten-z₂-preserves-length {_} {s} {p}))
        (cong₂ _*ₙ_ 
          (thm₁ {_} {_} {_} {s} flatten-zᵣ (flatten-z-isInplace) i)
          (thm₁ {_} {_} {_} {p} flatten-zᵣ (flatten-z-isInplace) j)
        )

  u-flatten-z-lemma : {s : S (ss (ss ℓ))} → u-flatten (flatten-z s) ≡ u-flatten s
  u-flatten-z-lemma {ℓ} {ι s} = refl
  u-flatten-z-lemma {ℓ} {s ⊗ p} rewrite u-flatten-z-lemma {_} {s} | u-flatten-z-lemma {_} {p} = refl

  help : {s : S (ss (ss ℓ))} {i : P s} →
       subst (λ z → P (ν z)) (u-flatten-z-lemma {_} {s}) ((i ⟨ rev flatten-zᵣ ⟩) ⟨ rev ν-flattenᵣ ⟩)
       ≡ (i ⟨ rev ν-flattenᵣ ⟩)
  help {ℓ} {.(ι _)} {ι i} = refl
  help {ℓ} {(s ⊗ p)} {i ⊗ j} with u-flatten-z-lemma {_} {s} | u-flatten-z-lemma {_} {p}
  ... | x | y = ?


  twiddles-rev-flatten-zᵣ-lemma : {s p
                                 : S (ss (ss ℓ))}
                                (i : P s) (j : P p) →
                                twiddles (i ⟨ rev flatten-zᵣ ⟩) (j ⟨ rev flatten-zᵣ ⟩) ≡
                                twiddles i j
  twiddles-rev-flatten-zᵣ-lemma {ℓ} {s} {p} i j = cong₂ -ω 
      (flatten-z₂-preserves-length {_} {s} {p}) 
      (cong₂ _*ₙ_ {iota′ ((i ⟨ rev flatten-zᵣ ⟩) ⟨ rev ν-flattenᵣ ⟩)} {iota′ (i ⟨ rev ν-flattenᵣ ⟩)} {iota′ ((j ⟨ rev flatten-zᵣ ⟩) ⟨ rev ν-flattenᵣ ⟩)} {iota′ (j ⟨ rev ν-flattenᵣ ⟩)} 
          (dcong₂ (λ a b → iota′ {a} b) {_} {_} {(i ⟨ rev flatten-zᵣ ⟩) ⟨ rev ν-flattenᵣ ⟩} {(i ⟨ rev ν-flattenᵣ ⟩)} (u-flatten-z-lemma {_} {s}) ?)
          ?
      )
            -- iota′ ((i ⟨ rev flatten-zᵣ ⟩) ⟨ rev ν-flattenᵣ ⟩) *ₙ
            -- iota′ ((j ⟨ rev flatten-zᵣ ⟩) ⟨ rev ν-flattenᵣ ⟩)
            -- ≡ iota′ (i ⟨ rev ν-flattenᵣ ⟩) *ₙ iota′ (j ⟨ rev ν-flattenᵣ ⟩)


  lemma₁ : ∀ (s : S (ss ℓ)) → transp (transp s) ≡ s
  lemma₁ {ℓ} (ι s) = refl
  lemma₁ {ℓ} (s ⊗ p) rewrite lemma₁ s | lemma₁ p = refl

  module _ (A : Set) (Pr : A → Set) where 
    thm : (f : A → A → A) 
        → (g : {x y : A} → (Pr x → Pr y → Pr (f x y))) 
        → (x a y b : A) 
        → (prf₁ : x ≡ a)
        → (prf₂ : y ≡ b)
        → (x′ : Pr x) (y′ : Pr y) 
        → subst Pr (cong₂ f prf₁ prf₂) (g x′ y′) ≡ g (subst Pr prf₁ x′) (subst Pr prf₂ y′)
    thm f g x .x y .y refl refl x′ y′ = refl
  
  lemma₂ : ∀ {s : S (ss ℓ)} {i : P s} → i ≡ subst P (lemma₁ s) (i ⟨ transpᵣ ⟩ ⟨ transpᵣ ⟩) 
  lemma₂ {ℓ} {ι s} {ι i} = refl
  lemma₂ {ℓ} {s ⊗ p} {i ⊗ j} =
    begin
      i ⊗ j
    ≡⟨ ? ⟩
      subst P (cong₂ _⊗_ (lemma₁ s) (lemma₁ p)) ((i ⊗ j) ⟨ transpᵣ ⟩ ⟨ transpᵣ ⟩)
    ≡⟨ ? ⟩
      subst P (lemma₁ (s ⊗ p)) ((i ⊗ j) ⟨ transpᵣ ⟩ ⟨ transpᵣ ⟩)
    ∎

  lemma₃ : ∀ {s : S (ss ℓ)} {i : P s} → i ⟨ transpᵣ ⟩ ⟨ transpᵣ ⟩ ≡ subst P (sym (lemma₁ s)) i
  lemma₃ {ℓ} {ι s} {ι i} = refl
  lemma₃ {ℓ} {s ⊗ p} {i ⊗ j} rewrite lemma₃ {i = i} | lemma₃ {i = j} = ?
  
  un-ν : ∀ {n : U} → P (ν n) → Fin (suc n)
  un-ν (ν i) = i

  open import Data.Fin.Properties

  lemma₅ : ∀ {n m : U} {i : P (ν n)} {j : P (ν m)} → iota′ (((ι i) ⊗ (ι j)) ⟨ unflat ⟩) ≡ toℕ ((combine (un-ν i) (un-ν j)))
  --toℕ {suc (iota′ j +ₙ iota′ i *ₙ suc (iota′ j))} (cast refl (combine (fromℕ (iota′ i)) (fromℕ (iota′ j)))) 
  lemma₅ {_} {_} {ν x} {ν y} = ?

  lemma₄ : {s : S (ss ℓ)} {i : P s} →
         iota′ (((i ⟨ transpᵣ ⟩) ⟨ transpᵣ ⟩) ⟨ rev ν-flattenᵣ ⟩) ≡ iota′ (i ⟨ rev ν-flattenᵣ ⟩)
  lemma₄ {ℓ} {ι s} {ι i} = refl
  lemma₄ {ℓ} {s ⊗ p} {i ⊗ j} = ? 
    {-rewrite 
      lemma₅ {_} {_} {(((i ⟨ transpᵣ ⟩) ⟨ transpᵣ ⟩) ⟨ rev ν-flattenᵣ ⟩)} {(((j ⟨ transpᵣ ⟩) ⟨ transpᵣ ⟩) ⟨ rev ν-flattenᵣ ⟩)} 
    | lemma₅ {_} {_} {(i ⟨ rev ν-flattenᵣ ⟩)} {(j ⟨ rev ν-flattenᵣ ⟩)}
    | lemma₄ {_} {_} {i}
    | lemma₄ {_} {_} {j}
    | lemma₁ s
      = refl-}

  twiddles-transₗ-lemma : {s p : S (ss ℓ)}
                        (i : P s) (j : P p) →
                        twiddles (i ⟨ transpᵣ ∙ transpᵣ ⟩) j ≡
                        twiddles i j
  twiddles-transₗ-lemma {ℓ} {s} {p} i j rewrite (resh-length {_} {_} {transp (transp s)} (transpᵣ ∙ transpᵣ)) 
      = cong (-ω _) (cong₂ _*ₙ_ {iota′ (((i ⟨ transpᵣ ⟩) ⟨ transpᵣ ⟩) ⟨ rev ν-flattenᵣ ⟩) } {iota′ (i ⟨ rev ν-flattenᵣ ⟩)} ? refl)

  dft≡fft : {s : S (ss zz)}
          (xs : Ar s ℂ) (i : P s) →
          dft (reshape flatten-zᵣ xs) (i ⟨ rev flatten-zᵣ ⟩) ≡
          reshape CMᵗ (fft dft twiddles xs) i
  dft≡fft {ι s} xs (ι i) = refl
  dft≡fft {s₁ ⊗ s₂} xs (i₁ ⊗ i₂) = ?


ℕ-dft : FFT-Specification
ℕ-dft = record {ℕ-dft′
               ; twiddles-flatten-zᵣ-lemma = λ {l} {s} {p} → ℕ-dft′.twiddles-flatten-zᵣ-lemma {_} {s} {p}
               }

--This email refers to Agda the programming language, not the Golgafrinchan junior personnel officer
{-
module _ where
  open ℕ-dft′
  open import Matrix.Simple.Base
  open import FFT.Simple.Base renaming (twiddles to Simp-twiddles; DFT to Simp-DFT)
  open import Matrix.SimpleLeveledRelation
  open import Data.Product

  twiddle-relation : ∀ {s₁ s₂ : S (ss zz)} → ∀ (i : P s₁) (j : P s₂) → twiddles ? ? ≡ Simp-twiddles cplx (P-from (i ⊗ j))
  --twiddles : Ar (s ⊗ p) ℂ
  --twiddles : ∀ {s p : S (ss ℓ)} → P s → P p → ℂ

-}


    --record
        -- { -- ℕ-dft′
        -- ; twiddles-CMᵗᵣ-lemma = ?
        -- ; twiddles-flatten-zᵣ-lemma = ?
        -- ; twiddles-rev-flatten-zᵣ-lemma = ?
        -- ; twiddles-transₗ-lemma = ?
        -- ; dft≡fft = ?
        -- }
