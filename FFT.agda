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

open import src.Matrix using (Ar; Shape; Position; ι; _⊗_; zipWith; nestedMap; length; foldr)
open import src.Matrix.Sum _+_ 0ℂ +-isCommutativeMonoid using (sum)
open import src.Reshape using (Reshape; transpose; transposeᵣ; rev; recursive-transposeᵣ; recursive-transpose; reshape; flat; _∙_; swap; _⟨_⟩; _♯; _⊕_; eq)

------------------------------------
--- DFT and FFT helper functions ---
------------------------------------

offset : ∀ {s : Shape} → Position s → Position (ι (length s))
offset i = i ⟨ _♯ ⟩

offset-n : ∀ {s : Shape} → Position s → ℕ
offset-n i with offset i
... | ι x = toℕ x

position-sum : ∀ {s r : Shape} → Position (s ⊗ r) → ℕ
position-sum {s} {r} (i ⊗ j) = offset-n i *ₙ offset-n j

-- There is 100% some relation between twiddles and step,
-- however I have had a brief play and havent found it yet

twiddles : ∀ {s r : Shape} → Ar (s ⊗ r) ℂ
twiddles {s} {r} p = -ω (length (s ⊗ r)) (position-sum p)

step : {N : ℕ} → {Fin N} → ℂ → ℕ → ℂ
step {N} {k} xₙ n = xₙ * (-ω N (n *ₙ (toℕ k)))

DFT : ∀ {N : ℕ} → Ar (ι N) ℂ → Ar (ι N) ℂ
DFT {N} xs (ι k) = sum (zipWith (step {N} {k}) xs offset-n)

FFT : ∀ {s : Shape} → Ar s ℂ → Ar (recursive-transpose s) ℂ
FFT {ι x     } arr = DFT arr -- Use the DFT when no splitting is defined 
FFT {sₗ  ⊗ sᵣ} arr = let innerDFTapplied       = nestedMap FFT (reshape swap arr) in
                     let twiddleFactorsApplied = zipWith _*_   innerDFTapplied twiddles in
                     let outerDFTapplied       = nestedMap FFT (reshape swap twiddleFactorsApplied) in
                     reshape swap outerDFTapplied

