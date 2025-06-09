module src.Matrix.ToStdVector where

open import Data.Nat
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec.Functional as Vector using (Vector)
open import src.Matrix

open import Function.Bundles
open import Relation.Binary.Bundles

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; subst; cong-app)
open Eq.≡-Reasoning

open import Level using (0ℓ) renaming (suc to lsuc)

open import src.Extensionality using (extensionality)

-- There is an isomorphism between std vectors and single dimensional matrixs, 
-- was going to use this to allow me to exploit std lib proofs (mainly:
-- https://agda.github.io/agda-stdlib/master/Algebra.Properties.Semiring.Sum.html#812
-- But couldn't get my head around using the propper isomorphsm ↔, so just implemented the above myself

variable
  X : Set
  N : ℕ

ar-to-vec : Ar (ι N) X → Vector X N
ar-to-vec arr p = arr (ι p)

ar-from-vec : Vector X N → Ar (ι N) X
ar-from-vec vec (ι x) = vec x

ar-from-vec∘vec-to-ar : ∀ (arr : Ar (ι N) X) → ar-from-vec (ar-to-vec arr) ≡ arr
ar-from-vec∘vec-to-ar {N} {X} arr = extensionality λ{(ι x) → refl }

ar-to-vec∘vec-to-from : ∀ (vec : Vector X N) → ar-to-vec (ar-from-vec vec) ≡ vec
ar-to-vec∘vec-to-from vec = refl


-- vec↔ar : ∀ {N : ℕ} {X : Set} → Ar (ι N) X ↔ Vector X N
-- vec↔ar = record
--           { to        = λ { x → ? }
--           ; from      = ? 
--           ; to-cong   = ? 
--           ; from-cong = ? 
--           ; inverse   = ? 
--           }
