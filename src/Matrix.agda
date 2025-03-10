module src.Matrix where

open import Data.Nat using (ℕ; _≡ᵇ_; suc; zero; _+_; _*_)
open import Data.Nat.Properties using (*-assoc; *-comm)
open import Data.Nat.DivMod using (_divMod_; _div_;_mod_)
open import Data.Fin as F using (Fin; toℕ; fromℕ; splitAt; remQuot) renaming (zero to fzero; suc to fsuc)
open import Data.Bool using (true; false)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)
open import Data.Sum.Base using (inj₁; inj₂)

open import Function.Base using (_$_; id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

private
  variable
    n m : ℕ
    X Y Z : Set

data Shape : Set where
  ι   : ℕ → Shape
  _⊗_ : Shape → Shape → Shape

private
  variable
    s p : Shape

-- Shape to... something
data Position : Shape → Set where
  ι   : Fin n → Position (ι n)
  _⊗_ : Position s → Position p → Position (s ⊗ p)


-- An array takes a shape and a set, and returns a method to access elements of the type of the given set
Ar : Shape → Set → Set
Ar s X = Position s → X

nil : Ar (ι 0) X
nil (ι ())

ι-cons : X → Ar (ι n) X → Ar (ι (suc n)) X
ι-cons x xs (ι  fzero  ) = x
ι-cons x xs (ι (fsuc i)) = xs (ι i)

length : Shape → ℕ
length (ι x) = x
length (s ⊗ s₁) = length s * length s₁

map : (X → Y) → Ar s X → Ar s Y
map f ar i = f (ar i)

-- Define my own version of equality
_==_ : ∀ {s : Shape} {X : Set} → Ar s X → Ar s X → Set
_==_ {s} xs ys = ∀ (p : Position s) → xs p ≡ ys p

nest : Ar (s ⊗ p) X → Ar s (Ar p X)
nest a i j = a (i ⊗ j)

unnest : Ar s (Ar p X) → Ar (s ⊗ p) X
unnest a (i ⊗ j) = a i j

nestedMap : ∀ {s p t : Shape} → (Ar p X → Ar t Y) → Ar (s ⊗ p) X → Ar (s ⊗ t) Y
nestedMap f ar = unnest (map f (nest ar))

mapMap : ∀ {X Y Z : Set} {f : X → Y} {g : Y → Z} {s : Shape} → map {X} {Z} {s} (g ∘ f) ≡ (map g) ∘ (map f)
mapMap = refl

_[_] : ∀ {X : Set} {s : Shape} → Ar s X → Position s → X
arr [ pos ] = arr pos

identityMatrix : ∀ { i : ℕ } → Ar (ι i ⊗ ι i) ℕ
identityMatrix (ι i ⊗ ι j) with (toℕ i) ≡ᵇ (toℕ j)
... | false = 0
... | true  = 1

head₁ : Ar (ι (suc n)) X → X
head₁ ar = ar (ι fzero)

tail₁ : Ar (ι (suc n)) X → Ar (ι n) X
tail₁ ar (ι x) = ar (ι (fsuc x))

foldr : ∀ {n : ℕ} {X Y : Set} → (X → Y → Y) → Y → Ar (ι n) X → Y
foldr {zero } f acc ar = acc
foldr {suc n} f acc ar = foldr f (f (head₁ ar) acc) (tail₁ ar)

zip : Ar (ι n) X → Ar (ι n) Y → Ar (ι n) (X × Y)
zip xs ys pos = ⟨ xs pos , ys pos ⟩

zipWith : (X → Y → Z) → Ar s X → Ar s Y → Ar s Z
zipWith f arr₁ arr₂ pos = f (arr₁ pos) (arr₂ pos)

_++_ : Ar (ι n) X → Ar (ι m) X → Ar (ι (n + m)) X
_++_ {n} {X} {m} arr₁ arr₂ (ι pos) with splitAt n {m} pos
... | inj₁ finN = arr₁ (ι finN)
... | inj₂ finM = arr₂ (ι finM)

-- foldZip : ∀ {n : ℕ} → (X → Y → Z → Z ) → Z → Ar (ι n) X → Ar (ι n) Y → Z
-- foldZip {X} {Y} {Z} {zero} f acc xs ys = acc
-- foldZip {X} {Y} {Z} {suc n} f acc xs ys = foldr f (f (head₁ xs) (head₁ ys) acc) (tail₁ xs) (tail₁ ys)

-- ar-⊗-assoc : ∀ {s t u : Shape} → Ar ((s ⊗ t) ⊗ u) X → Ar (s ⊗ (t ⊗ u)) X
-- ar-⊗-assoc arr (p ⊗ (p₁ ⊗ p₂)) = arr ((p ⊗ p₁) ⊗ p₂)
-- 
-- flattern-less-general : Ar (ι n ⊗ s) X → Ar (ι (n * length s)) X
-- flattern-less-general {n} {ι x₁} arr = flattern arr
-- flattern-less-general {n} {ι x₁ ⊗ s₁} {X} arr rewrite *-assoc n x₁ (length s₁) = flattern (unnest (map flattern-less-general (nest arr)))
-- flattern-less-general {n} {(s ⊗ s₂) ⊗ ι x₁} arr with 
-- flattern-less-general {n} {(s ⊗ s₂) ⊗ (s₁ ⊗ s₃)} arr x = ?
-- 

--flattern-general : Ar s X → Ar (ι (length s)) X
--flattern-general {ι x} arr = arr
--flattern-general {ι x ⊗ s} arr (ι p) with remQuot {x} (length s) p
--... | ⟨ fst , snd ⟩ = let sub-arr = (nest arr) (ι fst) in flattern-general sub-arr (ι snd)
--flattern-general {(s ⊗ s₁) ⊗ s₂} arr (ι p) with map flattern-general (nest arr) | remQuot {length (s ⊗ s₁)} (length s₂) p
--... | tmp1 | ⟨ fst , snd ⟩ = let tmp0 = map (λ arr → arr (ι snd)) tmp1 in flattern-general tmp0 (ι ?)

-- flattern-general {ι x} arr = arr
-- flattern-general {ι x ⊗ s₁} arr = flattern (unnest (map flattern-general (nest arr)))
-- flattern-general {(s ⊗ s₂) ⊗ s₁} arr rewrite *-assoc (length s) (length s₂) (length s₁) = flattern-general (unnest (map flattern-general (nest (ar-⊗-assoc arr)))) 
-- 
-- 
-- 
iterate : (n : ℕ) → (X → X) → X → Ar (ι n) X
iterate zero    f acc = nil
iterate (suc n) f acc = ι-cons acc (iterate n f (f acc))








