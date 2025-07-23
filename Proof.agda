open import src.Real using (Real)
open import src.Complex using (Cplx)

import Algebra.Structures as AlgebraStructures
import Algebra.Definitions as AlgebraDefinitions

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; subst; cong-app)
open Eq.≡-Reasoning

module Proof (real : Real) (cplx : Cplx real) where

open Real real using (_ᵣ; ℝ)
  renaming (_+_ to _+ᵣ_; _-_ to _-ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_; *-comm to *ᵣ-comm; *-identityʳ to *ᵣ-identityʳ)
open Cplx cplx using (ℂ; _+_; fromℝ; _*_; -ω; 0ℂ; +-*-isCommutativeRing; ω-r₁x-r₁y; ω-N-mN; ω-N-k₀+k₁)

open AlgebraStructures  {A = ℂ} _≡_
open AlgebraDefinitions {A = ℂ} _≡_

open IsCommutativeRing +-*-isCommutativeRing using (distribˡ; *-comm; zeroˡ; *-identityʳ; *-assoc; +-identityʳ; +-assoc; +-comm; +-identityˡ)

open import Data.Nat.Base using (ℕ; zero; suc) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties using (suc-injective) renaming (*-comm to *ₙ-comm; *-identityʳ to *ₙ-identityʳ; *-assoc to *ₙ-assoc; 
  +-identityʳ to +ₙ-identityʳ; *-zeroˡ to *ₙ-zeroˡ; *-zeroʳ to *ₙ-zeroʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
open import Data.Fin.Base using (Fin; quotRem; toℕ; combine; remQuot; quotient; remainder; cast; fromℕ<; _↑ˡ_; _↑ʳ_; splitAt; join) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (cast-is-id; remQuot-combine; splitAt-↑ˡ; splitAt-↑ʳ; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-combine; combine-remQuot; combine-surjective; toℕ-injective; toℕ-cast; cast-trans)

open import Data.Product.Base using (∃; ∃₂; _×_; proj₁; proj₂; map₁; map₂; uncurry) renaming ( _,_ to ⟨_,_⟩)
open import Data.Sum.Base using (inj₁; inj₂ )

open import src.Matrix using (Ar; Shape; _⊗_; ι; Position; nestedMap; zipWith; nest; map; unnest; head₁; tail₁; zip; iterate; ι-cons; nil; foldr; length; cong-foldr; splitAr; splitArₗ; splitArᵣ)
open import src.Matrix.Equality using (_≅_; foldr-cong; eq+eq≅arr; reduce-≅; tail₁-cong)
open import src.Matrix.Sum real cplx using (sum; sum-cong; sum-nil; sum-zeros; split-sum; foldr≡sum)
open import src.Matrix.Properties using (splitArᵣ-zero; tail₁-const; zipWith-congˡ)
open import src.Reshape using (reshape; Reshape; flat; _♭; _♯; recursive-transpose; recursive-transposeᵣ; _∙_; rev; _⊕_; swap; eq; split; _⟨_⟩; eq+eq; eq+eq-position-wrapper; reindex; rev-eq; flatten-reindex; |s|≡|sᵗ|)

open import Function.Base using (_$_; id; _∘_; flip; _∘₂_)

open import FFT real cplx 

private
  variable
    s : Shape

---------------------------------
--- Properties of DFT and FFT ---
---------------------------------

DFT-cong : ∀ {n : ℕ} {xs ys : Ar (ι n) ℂ} → xs ≅ ys → DFT xs ≅ DFT ys
DFT-cong {n} {xs} {ys} prf (ι x) = sum-cong (zipWith-congˡ {zs = offset-n} {f = (λ xₙ n₁ → xₙ * -ω n (n₁ *ₙ toℕ x))} prf )

FFT-cong : ∀ {s : Shape} {xs ys : Ar s ℂ} → xs ≅ ys → FFT xs ≅ FFT ys
FFT-cong {ι x   } {xs} {ys} prf i = DFT-cong prf i
FFT-cong {s ⊗ s₁} {xs} {ys} prf (i ⊗ i₁) = (FFT-cong {s₁} λ { j₁ → (cong₂ _*_ ((FFT-cong {s} λ {j₂ → prf (j₂ ⊗ j₁) }) i₁ ) refl) }) i

fft-ok : ∀ (arr : Ar s ℂ) → FFT arr ≅ ((reshape _♯) ∘ DFT ∘ (reshape flatten-reindex)) arr
fft-ok {ι x} arr i = refl
fft-ok {s ⊗ s₁} arr (i ⊗ j) =
  begin
    _ ≡⟨ fft-ok _ i ⟩
    _ ≡⟨ DFT-cong (λ x → cong₂ _*_ (fft-ok _ j) refl) (i ⟨ rev _♭ ⟩ ) ⟩
    _ ≡⟨⟩ ?












