open import Real using (Real)
open import Complex using (Cplx)

import Algebra.Structures as AlgebraStructures

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

module FFT (real : Real) (cplx : Cplx real) where
  open Cplx cplx using (ℂ; _*_; -ω; e^i_; _+_; 0ℂ; +-*-isCommutativeRing)

  open AlgebraStructures  {A = ℂ} _≡_
  open IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid)

  open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
  open import Data.Nat.Base using (ℕ; zero; suc; NonZero) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
  open import Data.Nat.Properties using (nonZero?)
  open import Relation.Nullary

  open import Matrix using (Ar; Shape; Position; ι; _⊗_; zipWith; mapRows; length)
  open import Matrix.Sum _+_ 0ℂ +-isCommutativeMonoid using (sum)
  open import Matrix.Reshape using (recursive-transpose; reshape; swap; _⟨_⟩; ♯; recursive-transposeᵣ)
  open import Matrix.NonZero using (NonZeroₛ; ι; _⊗_; nonZeroₛ-s⇒nonZero-s; nonZeroDec; nonZeroₛ-s⇒nonZeroₛ-sᵗ)

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
  offset-prod (k ⊗ j) = iota (k ⟨ ♯ ⟩) *ₙ iota (j ⟨ ♯ ⟩)

  twiddles : ⦃ nonZeroₛ-s⊗p : NonZeroₛ (s ⊗ p) ⦄ → Ar (s ⊗ p) ℂ
  twiddles {s} {p} ⦃ nonZeroₛ-s⊗p ⦄ i =
    -ω (length (s ⊗ p)) ⦃ (nonZeroₛ-s⇒nonZero-s (nonZeroₛ-s⊗p)) ⦄ (offset-prod i)

  -------------------
  --- DFT and FFT ---
  -------------------

  DFT′ : ∀ {N : ℕ} → ⦃ nonZero-N : NonZero N ⦄ → Ar (ι N) ℂ → Ar (ι N) ℂ
  DFT′ {N} ⦃ nonZero-N ⦄ xs j = sum (λ k → xs k * -ω N ⦃ nonZero-N ⦄ (iota k *ₙ iota j))

  FFT′ : ∀ {s : Shape} → ⦃ nonZero-s : NonZeroₛ s ⦄ → Ar s ℂ → Ar (recursive-transpose s) ℂ
  FFT′ {ι N} ⦃ ι nonZero-N ⦄ arr = DFT′ ⦃ nonZero-N ⦄ arr
  FFT′ {r₁ ⊗ r₂} ⦃ nonZero-r₁ ⊗ nonZero-r₂ ⦄ arr = 
      let 
          innerDFTapplied       = mapRows FFT′ (reshape swap arr)   
          twiddleFactorsApplied = zipWith _*_   innerDFTapplied twiddles
          outerDFTapplied       = mapRows FFT′ (reshape swap twiddleFactorsApplied) 
      in  reshape swap outerDFTapplied
      where
        instance
          _ : NonZeroₛ r₁
          _ = nonZero-r₁
          _ : NonZeroₛ r₂
          _ = nonZero-r₂
          _ : NonZeroₛ (r₂ ⊗ (recursive-transpose r₁))
          _ = nonZero-r₂ ⊗ (nonZeroₛ-s⇒nonZeroₛ-sᵗ nonZero-r₁)

  DFT : ∀ {N : ℕ} → Ar (ι N) ℂ → Ar (ι N) ℂ
  DFT {N} arr with nonZero? N
  ... | no  ¬nonZero-s = arr
  ... | yes  nonZero-s = DFT′ ⦃ nonZero-s ⦄ arr

  FFT : ∀ {s : Shape} → Ar s ℂ → Ar (recursive-transpose s) ℂ
  FFT {s} arr with nonZeroDec s
  ... | no  ¬nonZero-s = reshape (recursive-transposeᵣ) arr
  ... | yes  nonZero-s = FFT′ ⦃ nonZero-s ⦄ arr

