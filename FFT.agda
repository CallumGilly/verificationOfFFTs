open import Real using (Real)
open import Complex using (Cplx)

import Algebra.Structures as AlgebraStructures

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

module FFT (cplx : Cplx) where
  open Cplx cplx using (ℂ; _*_; -ω; _+_; 0ℂ; +-*-isCommutativeRing)

  open AlgebraStructures  {A = ℂ} _≡_
  open IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid)

  open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
  open import Data.Nat.Base using (ℕ; zero; suc; NonZero) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
  open import Data.Nat.Properties using (nonZero?; *-comm)
  open import Relation.Nullary
  open import Data.Empty

  open import Matrix using (Ar; Shape; Position; ι; _⊗_; zipWith; mapLeft; length; nest; unnest; map)
  open import Matrix.Sum _+_ 0ℂ +-isCommutativeMonoid using (sum)
  open import Matrix.Reshape using (recursive-transpose; reshape; swap; _⟨_⟩; ♯; recursive-transposeᵣ; _∙_; reindex; ♭)
  open import Matrix.NonZero using (NonZeroₛ; ι; _⊗_; nonZeroₛ-s⇒nonZero-s; nonZeroDec; nonZeroₛ-s⇒nonZeroₛ-sᵗ)

  open import Function

  private
    variable
      N : ℕ
      s p : Shape

  --------------------------------
  --- NonZero helper functions ---
  --------------------------------

  fin-nz : (N : ℕ) → Fin N → NonZero N
  fin-nz (suc n) i = _

  pos⇒nz : Position s → NonZeroₛ s
  pos⇒nz (ι i) = ι (fin-nz _ i)
  pos⇒nz (i ⊗ i₁) = pos⇒nz i ⊗ pos⇒nz i₁

  zs-nopos : ¬ NonZeroₛ s → Position s → ⊥
  zs-nopos ¬nz-s (ι {suc n} i) = ¬nz-s (ι (fin-nz _ i))
  zs-nopos ¬nz-s (i ⊗ i₁) = ¬nz-s (pos⇒nz (i ⊗ i₁)) 
  ------------------------------------
  --- DFT and FFT helper functions ---
  ------------------------------------

  iota : Ar (ι N) ℕ
  iota (ι i) = toℕ i

  offset-prod : Position (s ⊗ p) → ℕ
  offset-prod (k ⊗ j) = iota (k ⟨ ♯ ⟩) *ₙ iota (j ⟨ ♯ ⟩)

  twiddles : Ar (s ⊗ p) ℂ
  twiddles {s} {p} i with nonZeroDec (s ⊗ p)
  ... | no ¬nz = ⊥-elim (¬nz (pos⇒nz i))
  ... | yes nz = -ω (length (s ⊗ p)) ⦃ nonZeroₛ-s⇒nonZero-s nz ⦄ (offset-prod i)

  -------------------
  --- DFT and FFT ---
  -------------------

  DFT : ∀ {N} → Ar (ι N) ℂ → Ar (ι N) ℂ
  DFT {N} xs with nonZero? N
  ... | no ¬nz = λ { (ι j) → ⊥-elim (¬nz (fin-nz _ j)) }
  ... | yes nz = λ j → sum (λ k → xs k * -ω N ⦃ nz ⦄ (iota k *ₙ iota j))

  FFT : ∀ {s : Shape} → Ar s ℂ → Ar (recursive-transpose s) ℂ
  FFT {ι N} arr = DFT arr
  FFT {r₁ ⊗ r₂} arr = 
      let 
          innerDFTapplied       = mapLeft FFT (reshape swap arr)   
          twiddleFactorsApplied = zipWith _*_   innerDFTapplied twiddles
          outerDFTapplied       = mapLeft FFT (reshape swap twiddleFactorsApplied) 
      in  reshape swap outerDFTapplied
