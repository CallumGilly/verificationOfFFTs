open import Real using (Real)
open import Complex using (Cplx)

import Algebra.Structures as AlgebraStructures

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

module FFT-split (real : Real) where
  open Real.Real real using (ℝ; π; _*_; _+_; _-_; _/_; sin; cos; 0ℝ; +-*-isCommutativeRing; _ᵣ)

  open AlgebraStructures  {A = ℝ} _≡_
  open IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid)

  open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
  open import Data.Nat.Base using (ℕ; zero; suc; NonZero) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
  open import Data.Nat.Properties using (nonZero?; *-comm)
  open import Relation.Nullary
  open import Data.Product hiding (swap)

  open import Matrix using (Ar; Shape; Position; ι; _⊗_; zipWith; mapLeft; length; nest; unnest; map)
  open import Matrix.Sum _+_ 0ℝ +-isCommutativeMonoid using (sum)
  open import Matrix.Reshape using (recursive-transpose; reshape; swap; _⟨_⟩; ♯; recursive-transposeᵣ; _∙_; reindex; ♭; _⊕_; eq; split; flat; assoₗ; assoᵣ)
  open import Matrix.NonZero using (NonZeroₛ; ι; _⊗_; nonZeroₛ-s⇒nonZero-s; nonZeroDec; nonZeroₛ-s⇒nonZeroₛ-sᵗ)

  open import Function

  private
    variable
      N : ℕ
      s p : Shape

  REAL : Position (ι 2)
  REAL = ι fzero

  IMAG : Position (ι 2)
  IMAG = ι (fsuc fzero)

  ------------------------------
  --- Complex Roots of unity ---
  ------------------------------

  -ωᵣ : (n : ℕ) → (j : ℕ) → ℝ 
  -ωᵣ n j = cos (((2 ᵣ) * (j ᵣ) * π) / (n ᵣ)) 

  -ωᵢ : (n : ℕ) → (j : ℕ) → ℝ 
  -ωᵢ n j = sin (((2 ᵣ) * (j ᵣ) * π) / (n ᵣ)) 

  ------------------------------------
  --- DFT and FFT helper functions ---
  ------------------------------------

  iota : Ar (ι N) ℕ
  iota (ι i) = toℕ i

  offset-prod : Position (s ⊗ p) → ℕ
  offset-prod (k ⊗ j) = iota (k ⟨ ♯ ⟩) *ₙ iota (j ⟨ ♯ ⟩)

  twiddles : ⦃ nonZeroₛ-s⊗p : NonZeroₛ (s ⊗ p) ⦄ → Ar ((s ⊗ p) ⊗ ι 2) ℝ
  twiddles {s} {p} ⦃ nonZeroₛ-s⊗p ⦄ (i ⊗ ι fzero) = -ωᵣ (length (s ⊗ p)) (offset-prod i)
  twiddles {s} {p} ⦃ nonZeroₛ-s⊗p ⦄ (i ⊗ ι (fsuc fzero)) = -ωᵢ (length (s ⊗ p)) (offset-prod i)

--  -------------------
--  --- DFT and FFT ---
--  -------------------
--

  DFT′ : ∀ {N : ℕ} → ⦃ nonZero-N : NonZero N ⦄ → Ar (ι N ⊗ ι 2) ℝ → Ar (ι N ⊗ ι 2) ℝ
  DFT′ {N} ⦃ nonZero-N ⦄ xs (j ⊗ ι fzero)        = sum {N} (λ k → 
                                                      (xs (k ⊗ REAL) * -ωᵣ N (iota k *ₙ iota j)) 
                                                    - (xs (k ⊗ IMAG) * -ωᵢ N (iota k *ₙ iota j)) 
                                                    )
  DFT′ {N} ⦃ nonZero-N ⦄ xs (j ⊗ ι (fsuc fzero)) = sum {N} (λ k → 
                                                      (xs (k ⊗ REAL) * -ωᵢ N (iota k *ₙ iota j)) 
                                                    + (xs (k ⊗ IMAG) * -ωᵣ N (iota k *ₙ iota j)) 
                                                    )

  FFT-mixed-swap : ∀ {s : Shape} → ⦃ nonZero-s : NonZeroₛ s ⦄ → Ar (s ⊗ ι 2) ℝ → Ar (recursive-transpose s ⊗ ι 2) ℝ
  FFT-mixed-swap {ι N} ⦃ ι nonZero-N ⦄ arr = DFT′ ⦃ nonZero-N ⦄ arr
  FFT-mixed-swap {r₁ ⊗ r₂} ⦃ nonZero-r₁ ⊗ nonZero-r₂ ⦄ arr =
      let 
          arr′ = reshape (assoₗ ∙ (swap ⊕ eq)) arr
          innerDFTapplied       = reshape (swap ⊕ eq ∙ assoᵣ) $ mapLeft FFT-mixed-swap $ reshape (assoₗ ∙ swap ⊕ eq) arr
          twiddleFactorsApplied = reshape (swap ⊕ eq)         $ zipWith _*_             (reshape (swap ⊕ eq) innerDFTapplied) twiddles
          outerDFTapplied       = reshape (swap ⊕ eq ∙ assoᵣ) $ mapLeft FFT-mixed-swap $ reshape assoₗ twiddleFactorsApplied
      in  outerDFTapplied where
        instance
          _ : NonZeroₛ r₁
          _ = nonZero-r₁
          _ : NonZeroₛ r₂
          _ = nonZero-r₂
          _ : NonZeroₛ (r₂ ⊗ (recursive-transpose r₁))
          _ = nonZero-r₂ ⊗ (nonZeroₛ-s⇒nonZeroₛ-sᵗ nonZero-r₁)
--
--  {-
--  `ffti : NonZeroₛ s → Inp (ar s C) (ar s C)
--  `ffti (ι nz)      = dft nz
--  `ffti (_⊗_ {p = p} nzs nzp) = 
--    part-col (`ffti nzs) eq
--    >>> twid ⦃ nzs ⊗ nzp ⦄
--    >>> part-row (`ffti nzp) eq 
--    >>> copy (♯ ∙ reindex (*-comm (size p) _) ∙ ♭ ∙ swap) -- TODO: check whether this is correct
--  -}
--  FFT′′ : ∀ {s : Shape} → ⦃ nonZero-s : NonZeroₛ s ⦄ → Ar s ℂ → Ar s ℂ
--  FFT′′ {ι N} ⦃ ι nonZero-N ⦄ arr = DFT′ ⦃ nonZero-N ⦄ arr
--  FFT′′ {r₁ ⊗ r₂} ⦃ nonZero-r₁ ⊗ nonZero-r₂ ⦄ arr =
--    let 
--      innerDFTApplied = reshape swap $ mapLeft FFT′′ $ reshape swap $ arr
--      twiddlesApplied = zipWith _*_ innerDFTApplied twiddles
--      outerDFTApplied = mapLeft FFT′′ $ twiddlesApplied
--    in reshape (♯ ∙ reindex (*-comm (length r₂) _) ∙ ♭ ∙ swap) outerDFTApplied
--    where
--      instance
--        _ : NonZeroₛ r₁
--        _ = nonZero-r₁
--        _ : NonZeroₛ r₂
--        _ = nonZero-r₂
--        _ : NonZeroₛ (r₂ ⊗ (recursive-transpose r₁))
--        _ = nonZero-r₂ ⊗ (nonZeroₛ-s⇒nonZeroₛ-sᵗ nonZero-r₁)
--        _ : NonZeroₛ (r₁ ⊗ r₂)
--        _ = nonZero-r₁ ⊗ nonZero-r₂
--
  FFT′ : ∀ {s : Shape} → ⦃ nonZero-s : NonZeroₛ s ⦄ → Ar (s ⊗ ι 2) ℝ → Ar (recursive-transpose s ⊗ ι 2) ℝ
  FFT′ {ι N} ⦃ ι nonZero-N ⦄ arr = DFT′ ⦃ nonZero-N ⦄ arr
  FFT′ {r₁ ⊗ r₂} ⦃ nonZero-r₁ ⊗ nonZero-r₂ ⦄ arr = 
      let 
          innerDFTapplied       = reshape assoᵣ $ mapLeft FFT′ (reshape (assoₗ ∙ swap ⊕ eq) arr)   
          twiddleFactorsApplied = zipWith _*_   innerDFTapplied twiddles
          outerDFTapplied       = mapLeft FFT′ (reshape (assoₗ ∙ swap ⊕ eq) twiddleFactorsApplied) 
      in  reshape (swap ⊕ eq ∙ assoᵣ) outerDFTapplied
      where
        instance
          _ : NonZeroₛ r₁
          _ = nonZero-r₁
          _ : NonZeroₛ r₂
          _ = nonZero-r₂
          _ : NonZeroₛ (r₂ ⊗ (recursive-transpose r₁))
          _ = nonZero-r₂ ⊗ (nonZeroₛ-s⇒nonZeroₛ-sᵗ nonZero-r₁)

--  DFT : ∀ {N : ℕ} → Ar (ι N) ℂ → Ar (ι N) ℂ
--  DFT {N} arr with nonZero? N
--  ... | no  ¬nonZero-s = arr
--  ... | yes  nonZero-s = DFT′ ⦃ nonZero-s ⦄ arr
--
--  FFT : ∀ {s : Shape} → Ar s ℂ → Ar (recursive-transpose s) ℂ
--  FFT {s} arr with nonZeroDec s
--  ... | no  ¬nonZero-s = reshape (recursive-transposeᵣ) arr
--  ... | yes  nonZero-s = FFT′ ⦃ nonZero-s ⦄ arr
--
