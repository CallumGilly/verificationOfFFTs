module src.Matrix.Equality where

open import src.Matrix using (Shape; Position; Ar)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

private variable
  s : Shape
  X Y : Set

infix 4 _≅_
data _≅_ (arr : Ar s X) : Ar s X → Set where
  mat-refl : ∀ { i : Position s } → (arr i) ≡ (arr i) → arr ≅ arr

mat-sym : ∀ {xs ys : Ar s X} 
  → xs ≅ ys
    -------
  → ys ≅ xs
mat-sym {s} {X} {xs} {.xs} (mat-refl {i} x) = mat-refl {i = i} refl

mat-cong : ∀ (f : Ar s X → Y) {xs ys : Ar s X}   
  → xs ≅ ys
    -----------
  → f xs ≡ f ys
mat-cong f (mat-refl x) = refl

mat-trans : ∀ {xs ys zy : Ar s X}
  → xs ≅ ys
  → ys ≅ zy
    -------
  → xs ≅ zy
mat-trans (mat-refl refl) (mat-refl {i} refl) = mat-refl {i = i} refl

module ≅-Reasoning {A : Set} where

  infix  1 ≅-begin_
  infixr 2 step-≅-∣ step-≅-⟩
  infix  3 _∎-at_

  ≅-begin_ : ∀ {x y : Ar s A} → x ≅ y → x ≅ y
  ≅-begin x≅y  =  x≅y

  step-≅-∣ : ∀ (x : Ar s A) {y : Ar s A} → x ≅ y → x ≅ y
  step-≅-∣ x x≅y  =  x≅y

  step-≅-⟩ : ∀ (x : Ar s A) {y z : Ar s A} → y ≅ z → x ≅ y → x ≅ z
  step-≅-⟩ x y≅z x≅y  =  mat-trans x≅y y≅z

  syntax step-≅-∣ x x≅y      =  x ≅⟨⟩ x≅y
  syntax step-≅-⟩ x y≅z x≅y  =  x ≅⟨  x≅y ⟩ y≅z

  _∎-at_ : ∀ (x : Ar s A) → (i : Position s) → x ≅ x
  _∎-at_ {s} x i = mat-refl {i = i} refl

open ≅-Reasoning
