module src.Matrix.Equality where

open import src.Matrix using (Shape; Position; Ar; foldr; ι; _⊗_; tail₁)
open import src.Reshape using (reshape; eq; _⊕_; Reshape)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

private variable
  s p : Shape
  X Y : Set

infix 4 _≅_

_≅_ : ∀ {s : Shape} {X : Set} → Ar s X → Ar s X → Set
_≅_ {s} xs ys = ∀ (i : Position s) → xs i ≡ ys i

reduce-≅ : ∀ {n : ℕ} {X : Set} {xs ys : Ar (ι (suc n)) X} → xs ≅ ys → (tail₁ xs) ≅ (tail₁ ys)
reduce-≅ {n} {X} {xs} {ys} prf (ι i) rewrite prf (ι (fsuc i)) = refl

foldr-cong : ∀ {X Y : Set} {n : ℕ} → (f : X → Y → Y) → (acc : Y) → {xs ys : Ar (ι n) X} → xs ≅ ys → foldr f acc xs ≡ foldr f acc ys
foldr-cong {X} {Y} {zero } f acc {xs} {ys} prf = refl
foldr-cong {X} {Y} {suc n} f acc {xs} {ys} prf rewrite 
    prf (ι fzero) 
  | foldr-cong {X} {Y} {n} f (f (ys (ι fzero)) acc) {tail₁ xs} {tail₁ ys} (reduce-≅ prf)
  = refl

-- New eq+eq
eq+eq≅arr : ∀ {n m : ℕ} {X : Set} {xs : Ar (ι n ⊗ ι m) X} → reshape (eq ⊕ eq) xs ≅ xs
eq+eq≅arr (ι x ⊗ ι y) = refl
