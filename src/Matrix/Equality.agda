module src.Matrix.Equality where

open import src.Matrix using (Shape; Position; Ar; ι; tail₁)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

private variable
  n : ℕ
  s p : Shape
  X Y : Set

infix 4 _≅_

_≅_ : Ar s X → Ar s X → Set
_≅_ {s} xs ys = ∀ (i : Position s) → xs i ≡ ys i

reduce-≅ : 
  ∀ {xs ys : Ar (ι (suc n)) X} 
  → xs ≅ ys 
  -------------------------
  → (tail₁ xs) ≅ (tail₁ ys)
reduce-≅ {n} {X} {xs} {ys} prf (ι i) rewrite prf (ι (fsuc i)) = refl

tail₁-cong : 
  ∀ {xs ys : Ar (ι (suc n)) X} 
  → xs ≅ ys 
  ---------------------
  → tail₁ xs ≅ tail₁ ys 
tail₁-cong {n} {xs} {ys} prf (ι i) = prf (ι (fsuc i))
