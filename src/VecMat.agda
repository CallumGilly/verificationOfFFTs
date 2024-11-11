module src.VecMat where

open import src.Vector using (Vec)
open import src.Matrix using (Ar; Shape; Position; ι)
open import Data.Nat using (ℕ)
open import Data.Fin as F using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

-- Using PLFA definition of isomorphism as I cant currently get my head arround StdLib ↔
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_


private
  variable
    X : Set
    n : ℕ

vecToArr : Vec X n → Ar (ι n) X
vecToArr vec (ι i) = vec i

-- Only allowing this to accept a 1 dimensional array
arrToVec : Ar (ι n) X → Vec X n
arrToVec ar i = ar (ι i)

-- ar↔vec : Vec X n ≃ Ar (ι n) X
-- ar↔vec = record
--   { to      = vecToArr
--   ; from    = arrToVec
--   ; from∘to = λ{ vec → refl }
--   ; to∘from = λ{ ar → begin
--       vecToArr (arrToVec ar)
--     ≡⟨⟩
--       vecToArr ((λ i → ar (ι i)))
--     ≡⟨⟩
--       vecToArr ((λ i → ar (ι i)))
--     ≡⟨⟩
--       ?
-- 
--   }
--   }
-- 
