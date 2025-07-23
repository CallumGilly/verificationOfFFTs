module src.Matrix.Properties where

open import src.Matrix
open import src.Matrix.Equality

open import Data.Nat using (ℕ; _≡ᵇ_; suc; zero; _+_; _*_)
open import Data.Nat.Properties using (*-assoc; *-comm)
open import Data.Nat.DivMod using (_divMod_; _div_;_mod_)
open import Data.Fin as F using (Fin; toℕ; fromℕ; splitAt; remQuot; join) renaming (zero to fzero; suc to fsuc)
open import Data.Bool using (true; false)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)
open import Data.Sum.Base using (inj₁; inj₂; [_,_])

open import Function.Base using (_$_; id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong₂)
open Eq.≡-Reasoning

private
  variable
    n   : ℕ
    X Y : Set

tail₁-const : ∀ {n : ℕ} {c : X} → tail₁ {n} (λ i → c) ≅ (λ j → c)
tail₁-const (ι x) = refl

splitArᵣ-zero : ∀ {n : ℕ} (arr : Ar (ι n) X) → splitArᵣ {0} arr ≅ arr
splitArᵣ-zero arr (ι i) = refl

splitArₗ-zero : ∀ {n : ℕ} (arr : Ar (ι n) X) → splitArₗ {0} arr ≅ nil
splitArₗ-zero arr (ι ())
  
zipWith-congˡ : ∀ {s : Shape} {X Y Z : Set} {xs ys : Ar s X} {zs : Ar s Y} {f : X → Y → Z} → xs ≅ ys → zipWith f xs zs ≅ zipWith f ys zs
zipWith-congˡ {s} {X} {Y} {Z} {xs} {ys} {zs} {f} prf i = cong₂ f (prf i) refl

zipWith-congʳ : ∀ {s : Shape} {X Y Z : Set} {xs : Ar s X} {ys zs : Ar s Y} {f : X → Y → Z} → ys ≅ zs → zipWith f xs ys ≅ zipWith f xs zs
zipWith-congʳ {s} {X} {Y} {Z} {xs} {ys} {zs} {f} prf i = cong₂ f refl    (prf i)
