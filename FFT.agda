open import src.Real using (Real)
open import src.Complex using (Cplx)

import Algebra.Structures as AlgebraStructures

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

module FFT (real : Real) (cplx : Cplx real) where
  open Cplx cplx using (ℂ; _*_; -ω; e^i_; _+_; 0ℂ; +-*-isCommutativeRing)

  open AlgebraStructures  {A = ℂ} _≡_
  open IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid)

  open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
  open import Data.Nat.Base using (ℕ; suc; NonZero) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
  open import Data.Nat.Properties using (m*n≢0)

  open import Matrix using (Ar; Shape; Position; ι; _⊗_; zipWith; nestedMap; length; NonZeroₛ; s⊗p-nonZeroₛ⇒s-nonZeroₛ; s⊗p-nonZeroₛ⇒p-nonZeroₛ)
  open import Matrix.Sum _+_ 0ℂ +-isCommutativeMonoid using (sum)
  open import Matrix.Reshape using (recursive-transpose; reshape; swap; _⟨_⟩; ♯; s-nonZeroₛ⇒sᵗ-nonZeroₛ)

  private
    variable
      N : ℕ
      s p : Shape

  ------------------------------------
  --- DFT and FFT helper functions ---
  ------------------------------------

  iota : Ar (ι N) ℕ
  iota (ι i) = toℕ i

  offset-prod : Position (s ⊗ p) → ℕ
  offset-prod (i ⊗ j) = iota (i ⟨ ♯ ⟩) *ₙ iota (j ⟨ ♯ ⟩)

  twiddles : ⦃ nonZeroₛ-s : NonZeroₛ s ⦄ → ⦃ nonZeroₛ-p : NonZeroₛ p ⦄ → Ar (s ⊗ p) ℂ
  twiddles {s} {p} ⦃ record { nonZeroₛ = nonZero-|s| } ⦄ ⦃ record { nonZeroₛ = nonZero-|p| } ⦄ i = 
    let instance 
      _ : NonZero (length (s ⊗ p))
      _ = m*n≢0 (length s) (length p) ⦃ nonZero-|s| ⦄ ⦃ nonZero-|p| ⦄
    in -ω (length (s ⊗ p)) (offset-prod i)

  -------------------
  --- DFT and FFT ---
  -------------------

  DFT : ∀ {N : ℕ} → ⦃ _ : NonZero N ⦄ → Ar (ι N) ℂ → Ar (ι N) ℂ
  DFT {N} xs k = sum (λ i → xs i * -ω N (offset-prod (i ⊗ k)))

  FFT : ∀ {s : Shape} → ⦃ nonZero-s : NonZeroₛ s ⦄ → Ar s ℂ → Ar (recursive-transpose s) ℂ
  FFT {ι N} ⦃ record { nonZeroₛ = nonZero-N } ⦄ arr = DFT ⦃ nonZero-N ⦄ arr -- Use the DFT when no splitting is defined 
  FFT {r₁  ⊗ r₂} ⦃ nonZero-s ⦄ arr = let instance
                                        nonZeroₛ-r₁  : NonZeroₛ r₁
                                        nonZeroₛ-r₁  = s⊗p-nonZeroₛ⇒s-nonZeroₛ {r₁} {r₂} ⦃ nonZero-s ⦄ 
                                        nonZeroₛ-r₂  : NonZeroₛ r₂
                                        nonZeroₛ-r₂  = s⊗p-nonZeroₛ⇒p-nonZeroₛ {r₁} {r₂} ⦃ nonZero-s ⦄ 
                                        nonZeroₛ-r₁ᵗ : NonZeroₛ (recursive-transpose r₁)
                                        nonZeroₛ-r₁ᵗ = s-nonZeroₛ⇒sᵗ-nonZeroₛ {r₁} ⦃ nonZeroₛ-r₁ ⦄
                                     in
                                     let innerDFTapplied       = nestedMap (FFT ⦃ nonZeroₛ-r₁ ⦄) (reshape swap arr)   
                                         twiddleFactorsApplied = zipWith _*_   innerDFTapplied (twiddles ⦃ nonZeroₛ-r₂ ⦄ ⦃ nonZeroₛ-r₁ᵗ ⦄)   
                                         outerDFTapplied       = nestedMap (FFT ⦃ nonZeroₛ-r₂ ⦄) (reshape swap twiddleFactorsApplied) 
                                     in
                                     reshape swap outerDFTapplied
