module Matrix.Properties where

open import Matrix
open import Matrix.Equality

open import Data.Nat using (ℕ)
open import Function.Base using (_∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong₂)

private
  variable
    n   : ℕ
    s     : Shape
    X Y Z : Set

tail₁-const : 
  ∀ {c : X} 
  ---------------------------------
  → tail₁ {n} (λ i → c) ≅ (λ j → c)
tail₁-const (ι x) = refl

splitArᵣ-zero : 
  ∀ (arr : Ar (ι n) X) 
  ------------------------
  → splitArᵣ {0} arr ≅ arr
splitArᵣ-zero arr (ι i) = refl

splitArₗ-zero : 
  ∀ (arr : Ar (ι n) X) 
  ------------------------
  → splitArₗ {0} arr ≅ nil
splitArₗ-zero arr (ι ())
  
zipWith-congˡ : 
  ∀ {xs ys : Ar s X} 
    {zs    : Ar s Y} 
    {f : X → Y → Z } 
  →  xs ≅ ys 
  -----------------------------------
  → zipWith f xs zs ≅ zipWith f ys zs
zipWith-congˡ {f = f} prf i = cong₂ f (prf i) refl

zipWith-congʳ : 
  ∀ {xs    : Ar s X} 
    {ys zs : Ar s Y} 
    {f : X → Y → Z }
  →  ys ≅ zs 
  ------------------------------------
  →  zipWith f xs ys ≅ zipWith f xs zs
zipWith-congʳ {f = f} prf i = cong₂ f refl    (prf i)

mapMap : 
  ∀ {f : X → Y} 
    {g : Y → Z} 
  ---------------------------------------------
  → map {X} {Z} {s} (g ∘ f) ≡ (map g) ∘ (map f)
mapMap = refl
