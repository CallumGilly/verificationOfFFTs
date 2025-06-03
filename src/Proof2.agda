open import src.Real using (Real)
module src.Proof2 (r : Real) where
open import Data.Nat.Base using (ℕ; suc; zero) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties using (*-comm; _≟_) renaming (*-zeroʳ to *ₙ-zeroʳ; *-zeroˡ to *ₙ-zeroˡ)
open import Data.Fin.Base using (Fin; quotRem; toℕ; combine; remQuot; quotient; remainder; cast) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (cast-is-id)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)

open import src.Matrix using (Ar; Shape; _⊗_; ι; Position; nestedMap; zipWith; nest; map; unnest; head₁; tail₁; zip; iterate; ι-cons; nil; foldr; length; cong-foldr)
open import src.Reshape using (reshape; Reshape; flat; _♭; _♯; recursive-transpose; recursive-transposeᵣ; _∙_; rev; _⊕_; swap; eq; split; _⟨_⟩; eq+eq; _♭₂; comm-eq; eq+eq-position-wrapper)
open import src.Complex r using (ℂ; _*_; _+_; ℂfromℕ; -ω; +-identityʳ; ω-N-0; *-identityʳ; _+_i; *-assoc; *-zeroₗ)
open ℂ using (real; imaginary)
open import src.FFT r using (FFT; twiddles; position-sum; offset-n)
open import src.DFTMatrix r using (DFT; posVec; step)
open import src.Extensionality using (extensionality)
open import Relation.Nullary using (Dec; yes; no)
open Real r using (ℝ; π; sin; cos; double-negative; _ᵣ; -ᵣ-identityʳ; *ᵣ-zeroᵣ; +ᵣ-identityˡ; *ᵣ-identityʳ; /ᵣ-zeroₜ; +ᵣ-identityʳ; +ᵣ-assoc; +ᵣ-comm)
  renaming (_+_ to _+ᵣ_; _-_ to _-ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_)

open import Function.Base using (_$_; id; _∘_; flip; _∘₂_)

open import src.MatrixEquality as MatEq
open MatEq using (_≅_; mat-refl)
open MatEq.≅-Reasoning


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; subst; cong-app)
open Eq.≡-Reasoning

-- Lifted from Proof.agda
fft₂-fold-equiv : ∀ {n m : ℕ} {arr : Ar (ι n ⊗ ι m) ℂ} {x : Fin n} {y : Fin m} →
  (FFT arr) ((ι y) ⊗ (ι x)) ≡ foldr 
          _+_ 
          (ℂfromℕ 0) 
          (λ p₀ → 
            (
              (
                foldr 
                  _+_ 
                  (ℂfromℕ 0)
                  (λ p₁ → (arr (p₁ ⊗ p₀)) * (-ω n ((posVec {n} p₁) *ₙ (toℕ y)))) 
              )
              * 
              (-ω (n *ₙ m) (position-sum (ι y ⊗ p₀)))
            )
            *
            (-ω m ((posVec {m} p₀) *ₙ (toℕ x)))
          )
fft₂-fold-equiv = ?

from-ι : ∀ {n : ℕ} → Position (ι n) → Fin n
from-ι (ι x) = x
dft-fold-equiv : ∀ 
  {n m : ℕ} 
  {arr : Ar (ι n ⊗ ι m) ℂ} 
  {x : Fin n} 
  {y : Fin m} 
  → 
  (((reshape _♯) ∘ DFT ∘ (reshape {ι n ⊗ ι m} _♭₂)) arr) (ι y ⊗ ι x) 
  ≡ 
    foldr 
      {m *ₙ n } 
      _+_ 
      (ℂfromℕ 0) 
      (λ absPos → 
        (arr (absPos ⟨ comm-eq (*-comm n m) ⟩ ⟨ flat ⟩)) 
        * 
        (-ω (m *ₙ n) ((posVec absPos) *ₙ (toℕ (combine y x))))
      )
dft-fold-equiv {n} {m} {arr} {x} {y} =
  begin
    (reshape _♯ ∘ DFT ∘ reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq)) arr (ι y ⊗ ι x)
  ≡⟨⟩
    (reshape _♯ (DFT (reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq) arr))) (ι y ⊗ ι x)
  ≡⟨⟩
    ((DFT (reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq) arr))) ((ι y ⊗ ι x) ⟨ _♯ {ι m ⊗ ι n } ⟩ )
  ≡⟨⟩
    ((DFT (reshape (comm-eq (*-comm n m) ∙ flat) (reshape (eq ⊕ eq) arr)))) ((ι y ⊗ ι x) ⟨ _♯ {ι m ⊗ ι n } ⟩ )
  ≡⟨ cong
      (λ f → ((DFT (reshape (comm-eq (*-comm n m) ∙ flat) (f)))) ((ι y ⊗ ι x) ⟨ _♯ {ι m ⊗ ι n } ⟩ ))
      (eq+eq arr)
   ⟩
    ((DFT (reshape (comm-eq (*-comm n m) ∙ flat) arr))) ((ι y ⊗ ι x) ⟨ _♯ {ι m ⊗ ι n } ⟩ )
  ≡⟨⟩
    foldr {m *ₙ n } _+_ (ℂfromℕ 0) (zipWith step (reshape (comm-eq (*-comm n m) ∙ flat) arr) posVec)
  ≡⟨⟩
    foldr {m *ₙ n } _+_ (ℂfromℕ 0) (λ absPos → step (arr (absPos ⟨ comm-eq (*-comm n m) ⟩ ⟨ flat ⟩)) (posVec absPos))
  ≡⟨⟩
    foldr 
      {m *ₙ n } 
      _+_ 
      (ℂfromℕ 0) 
      (λ absPos → 
        (arr (absPos ⟨ comm-eq (*-comm n m) ⟩ ⟨ flat ⟩)) 
        * 
        (-ω (m *ₙ n) ((posVec absPos) *ₙ (toℕ (combine y x))))
      )
  ∎



theorm-on-folds : ∀ 
  {r₁ r₂ : ℕ} 
  {arr : Ar (ι r₁ ⊗ ι r₂) ℂ} 
  {j₀ : Fin r₁} 
  {j₁ : Fin r₂} 
  →
  foldr 
    _+_ 
    (ℂfromℕ 0) 
    (λ{ (k₀) → 
      (
        (
          foldr 
            _+_ 
            (ℂfromℕ 0)
            (λ k₁ → (arr (k₁ ⊗ (k₀))) * (-ω r₁ ((posVec {r₁} k₁) *ₙ (toℕ j₁)))) 
        )
        * 
        (-ω (r₁ *ₙ r₂) (position-sum (ι j₁ ⊗ (k₀))))
      )
      *
      (-ω r₂ ((posVec {r₂} (k₀)) *ₙ (toℕ j₀)))
    })
  ≡
  foldr 
    _+_ 
    (ℂfromℕ 0) 
    (λ k → 
      (arr (k ⟨ comm-eq (*-comm r₁ r₂) ⟩ ⟨ flat ⟩)) 
      * 
      (-ω (r₂ *ₙ r₁) ((posVec k) *ₙ (toℕ (combine j₁ j₀))))
    )
theorm-on-folds {r₁} {r₂} {arr} {j₀} {j₁} =
  begin
    foldr 
      _+_ 
      (ℂfromℕ 0) 
      (λ{ (k₀) → 
        (
          (
            foldr 
              _+_ 
              (ℂfromℕ 0)
              (λ k₁ → (arr (k₁ ⊗ (k₀))) * (-ω r₁ ((posVec {r₁} k₁) *ₙ (toℕ j₁)))) 
          )
          * 
          (-ω (r₁ *ₙ r₂) (position-sum (ι j₁ ⊗ (k₀))))
        )
        *
        (-ω r₂ ((posVec {r₂} (k₀)) *ₙ (toℕ j₀)))
      })
  ≡⟨⟩
    ?
    
 

theorm : ∀ {n m : ℕ}
  → FFT ≡ (reshape _♯) ∘ DFT ∘ (reshape {ι n ⊗ ι m} _♭₂)
theorm {n} {m} =
  extensionality λ{arr → 
    extensionality λ{ (ι y ⊗ ι x) →
      begin
        (FFT arr) ((ι y) ⊗ (ι x))
      ≡⟨ fft₂-fold-equiv {n} {m} {arr} {x} {y} ⟩
        foldr 
          _+_ 
          (ℂfromℕ 0) 
          (λ p₀ → 
            (
              (
                foldr 
                  _+_ 
                  (ℂfromℕ 0)
                  (λ p₁ → (arr (p₁ ⊗ p₀)) * (-ω n ((posVec {n} p₁) *ₙ (toℕ y)))) 
              )
              * 
              (-ω (n *ₙ m) (position-sum (ι y ⊗ p₀)))
            )
            *
            (-ω m ((posVec {m} p₀) *ₙ (toℕ x)))
          )
      ≡⟨ theorm-on-folds {n} {m} {arr} {x} {y} ⟩
        foldr 
          {m *ₙ n } 
          _+_ 
          (ℂfromℕ 0) 
          (λ absPos → 
            (arr (absPos ⟨ comm-eq (*-comm n m) ⟩ ⟨ flat ⟩)) 
            * 
            (-ω (m *ₙ n) ((posVec absPos) *ₙ (toℕ (combine y x))))
          )
      ≡⟨ sym (dft-fold-equiv {n} {m} {arr} {x} {y}) ⟩
        (reshape _♯ ∘ DFT ∘ reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq)) arr (ι y ⊗ ι x)
      ∎

    }
  }
 
 





