open import src.Real using (Real)
open import src.Complex using (Cplx)

import Algebra.Structures as AlgebraStructures

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

module FFT (real : Real) (cplx : Cplx real) where
open Cplx cplx using (ℂ; _*_; -ω; e^i_; _+_; 0ℂ; +-*-isCommutativeRing)

open AlgebraStructures  {A = ℂ} _≡_
open IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid)

open import Function using (_$_; _∘_)

open import Data.Fin.Base using (Fin; toℕ; opposite) renaming (zero to fzero; suc to fsuc)
open import Data.Nat.Base using (ℕ; suc) renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)

open import src.Matrix using (Ar; Shape; Position; ι; _⊗_; zipWith; nestedMap; length)
open import src.Matrix.Sum _+_ 0ℂ +-isCommutativeMonoid using (sum)
open import src.Reshape using (Reshape; transpose; transposeᵣ; rev; recursive-transposeᵣ; recursive-transpose; reshape; flat; _∙_; swap; _⟨_⟩; _♯; _⊕_; eq)

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
offset-prod (i ⊗ j) = iota (i ⟨ _♯ ⟩) *ₙ iota (j ⟨ _♯ ⟩)

twiddles : Ar (s ⊗ p) ℂ
twiddles {s} {p} i = -ω (length (s ⊗ p)) (offset-prod i)

-------------------
--- DFT and FFT ---
-------------------

DFT : ∀ {N : ℕ} → Ar (ι N) ℂ → Ar (ι N) ℂ
DFT {N} xs k = sum (λ i → xs i * -ω N (offset-prod (i ⊗ k)))

FFT : ∀ {s : Shape} → Ar s ℂ → Ar (recursive-transpose s) ℂ
FFT {ι x     } arr = DFT arr -- Use the DFT when no splitting is defined 
FFT {sₗ  ⊗ sᵣ} arr = let innerDFTapplied       = nestedMap FFT (reshape swap arr) in
                     let twiddleFactorsApplied = zipWith _*_   innerDFTapplied twiddles in
                     let outerDFTapplied       = nestedMap FFT (reshape swap twiddleFactorsApplied) in
                     reshape swap outerDFTapplied

