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
  open import Data.Nat.Base using (ℕ; suc) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)

  open import Matrix using (Ar; Shape; Position; ι; _⊗_; zipWith; nestedMap; length)
  open import Matrix.Sum _+_ 0ℂ +-isCommutativeMonoid using (sum)
  open import Matrix.Reshape using (recursive-transpose; reshape; swap; _⟨_⟩; ♯)

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

  twiddles : Ar (s ⊗ p) ℂ
  twiddles {s} {p} i = -ω (length (s ⊗ p)) (offset-prod i)

  -------------------
  --- DFT and FFT ---
  -------------------

  DFT : ∀ {N : ℕ} → Ar (ι N) ℂ → Ar (ι N) ℂ
  DFT {N} xs k = sum (λ i → xs i * -ω N (offset-prod (i ⊗ k)))

  FFT : ∀ {s : Shape} → Ar s ℂ → Ar (recursive-transpose s) ℂ
  FFT {ι N     } arr = DFT arr -- Use the DFT when no splitting is defined 
  FFT {r₁  ⊗ r₂} arr = let innerDFTapplied       = nestedMap FFT (reshape swap arr) in
                       let twiddleFactorsApplied = zipWith _*_   innerDFTapplied twiddles in
                       let outerDFTapplied       = nestedMap FFT (reshape swap twiddleFactorsApplied) in
                       reshape swap outerDFTapplied

