open import src.Real using (Real)
module src.Proof (r : Real) where

open import Data.Nat.Base using (ℕ; suc; zero) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties using (*-zeroʳ)
open import Data.Fin.Base using (Fin; quotRem; toℕ; combine; remQuot) renaming (zero to fzero; suc to fsuc)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)

open import src.Matrix using (Ar; Shape; _⊗_; ι; _==_; Position; nestedMap; zipWith; nest; map; unnest; head₁; zip; iterate; ι-cons; nil; foldr; length)
open import src.Reshape using (reshape; Reshape; flat; _♭; _♯; recursive-transpose; recursive-transposeᵣ; _∙_; rev; flatten; _⊕_; swap; eq; split; _⟨_⟩; reshape-reshape; eq+eq)
open import src.Complex r using (ℂ; _*_; _+_; ℂfromℕ; -ω; +-identityʳ; ω-N-0; *-identityʳ; _+_i)
open ℂ using (real; imaginary)
open import src.FFT r using (FFT; twiddles; position-sum; FFT₁)
open import src.DFTMatrix r using (DFT; posVec; step)
open import src.Extensionality using (extensionality)
open Real r using (ℝ; π; sin; cos; double-negative; _ᵣ; -ᵣ-identityʳ; *ᵣ-zeroᵣ; +ᵣ-identityˡ; *ᵣ-identityʳ; /ᵣ-zeroₜ; +ᵣ-identityʳ)
  renaming (_+_ to _+ᵣ_; _-_ to _-ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_)

open import Function.Base using (_$_; id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

theorm₇ : ∀ {s : Shape} → FFT₁ {s} ≡ (DFT ∘ reshape _♭)
theorm₇ {ι x} = refl
theorm₇ {s ⊗ s₁} =
  extensionality λ{ arr → 
    extensionality λ{ (ι p) → 
      begin
        FFT₁ arr (ι p)
      ≡⟨⟩
        reshape 
          (flat ∙ swap)
          (nestedMap FFT₁ 
            (reshape 
              swap 
              (zipWith _*_ (nestedMap FFT₁ arr) twiddles)
            )
          )
          (ι p)
      ≡⟨ cong (λ f → reshape (flat ∙ swap) (nestedMap FFT₁ (reshape swap (zipWith _*_ (nestedMap f arr) twiddles))) (ι p)) theorm₇ ⟩
        reshape 
          (flat ∙ swap)
          (nestedMap FFT₁ 
            (reshape 
              swap 
              (zipWith _*_ (nestedMap (DFT ∘ reshape _♭) arr) twiddles)
            )
          )
          (ι p)
      ≡⟨ cong (λ f → reshape (flat ∙ swap) (nestedMap f (reshape swap (zipWith _*_ (nestedMap (DFT ∘ reshape _♭) arr) twiddles))) (ι p)) theorm₇ ⟩
        reshape 
          (flat ∙ swap)
          (nestedMap (DFT ∘ reshape _♭)
            (reshape 
              swap 
              (zipWith _*_ (nestedMap (DFT ∘ reshape _♭) arr) twiddles)
            )
          )
          (ι p)
      ≡⟨⟩
        map DFT (
        map (reshape _♭) (
          nest (reshape swap (zipWith _*_ (unnest (map DFT (map (reshape _♭) (nest arr)))) twiddles))
        )) (ι (proj₂ (remQuot {length s} (length s₁) p))) (ι (proj₁ (remQuot {length s} (length s₁) p)))
      ≡⟨⟩
        foldr _+_ ((0 ᵣ) + 0 ᵣ i)
            (λ pos →
               ((((real      (innerDFT arr pos p) *ᵣ cos (θ₂ pos p))
                  -ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p)))
                 *ᵣ cos (θ pos p))
                -ᵣ
                (((real      (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))
                  +ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)))
                 *ᵣ sin (θ pos p)))
               +
                (((real      (innerDFT arr pos p) *ᵣ cos (θ₂ pos p))
                  -ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p)))
                 *ᵣ sin (θ pos p))
                +ᵣ
                (((real      (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))
                  +ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)))
                 *ᵣ cos (θ pos p))
               i)
      ≡⟨⟩
        ?
    }
  }
  where
    θ : (pos : Position (ι (length s))) → (p : Fin (length s *ₙ length s₁)) → ℝ
    θ pos p = ((-ᵣ 2 ᵣ *ᵣ π *ᵣ
                  (posVec pos *ₙ toℕ (proj₂ (quotRem {length s} (length s₁) p))) ᵣ)
                 /ᵣ (length s ᵣ))
    θ₂ : (pos : Position (ι (length s))) → (p : Fin (length s *ₙ length s₁)) → ℝ
    θ₂ pos p = (-ᵣ 2 ᵣ *ᵣ π *ᵣ
                    (position-sum {s} (pos ⟨ _♭ ⟩) *ₙ
                     position-sum (ι (proj₁ (quotRem {length s} (length s₁) p))))
                    ᵣ)
                   /ᵣ ((length s *ₙ length s₁) ᵣ)
    innerDFT : (arr : Ar (s ⊗ s₁) ℂ) → (pos : Position (ι (length s))) → (p : Fin (length s *ₙ length s₁)) → ℂ
    innerDFT arr pos p = (foldr _+_ ((0 ᵣ) + 0 ᵣ i)
                    (λ pos₁ →
                       ((real (arr ((pos ⟨ _♭ ⟩) ⊗ (pos₁ ⟨ _♭ ⟩))) *ᵣ
                         cos
                         ((-ᵣ 2 ᵣ *ᵣ π *ᵣ
                           (posVec pos₁ *ₙ toℕ (proj₁ (quotRem {length s} (length s₁) p))) ᵣ)
                          /ᵣ (length s₁ ᵣ)))
                        -ᵣ
                        (imaginary (arr ((pos ⟨ _♭ ⟩) ⊗ (pos₁ ⟨ _♭ ⟩))) *ᵣ
                         sin
                         ((-ᵣ 2 ᵣ *ᵣ π *ᵣ
                           (posVec pos₁ *ₙ toℕ (proj₁ (quotRem {length s} (length s₁) p))) ᵣ)
                          /ᵣ (length s₁ ᵣ))))
                       +
                       (real (arr ((pos ⟨ _♭ ⟩) ⊗ (pos₁ ⟨ _♭ ⟩))) *ᵣ
                        sin
                        ((-ᵣ 2 ᵣ *ᵣ π *ᵣ
                          (posVec pos₁ *ₙ toℕ (proj₁ (quotRem {length s} (length s₁) p))) ᵣ)
                         /ᵣ (length s₁ ᵣ)))
                       +ᵣ
                       (imaginary (arr ((pos ⟨ _♭ ⟩) ⊗ (pos₁ ⟨ _♭ ⟩))) *ᵣ
                        cos
                        ((-ᵣ 2 ᵣ *ᵣ π *ᵣ
                          (posVec pos₁ *ₙ toℕ (proj₁ (quotRem {length s} (length s₁) p))) ᵣ)
                         /ᵣ (length s₁ ᵣ)))
                       i))


lemma₁ : ∀ 
  {s s₁ : Shape}
  {pos  : Position (ι (length s₁))}
  {p    : Fin (length s *ₙ length s₁)}
  → 
    (((posVec pos *ₙ toℕ                                        p)   ᵣ) /ᵣ ((length s *ₙ length s₁) ᵣ)) 
  ≡ 
    (((posVec pos *ₙ toℕ {length s} (proj₂ (quotRem {length s} (length s₁) p))) ᵣ) /ᵣ ( length s               ᵣ))
lemma₁ {s} {s₁} {ι x} {p} =
  begin
    (((posVec (ι x) *ₙ toℕ p) ᵣ) /ᵣ ((length s *ₙ length s₁) ᵣ))
  ≡⟨⟩
    (((toℕ x *ₙ toℕ p) ᵣ) /ᵣ ((length s *ₙ length s₁) ᵣ))
  ≡⟨⟩
    ?






