module src.Matrix where

open import Data.Nat using (ℕ; _≡ᵇ_; suc; zero; _+_; _*_)
open import Data.Nat.Properties using (*-assoc; *-comm)
open import Data.Nat.DivMod using (_divMod_; _div_;_mod_)
open import Data.Fin as F using (Fin; toℕ; fromℕ; splitAt; remQuot; join) renaming (zero to fzero; suc to fsuc)
open import Data.Bool using (true; false)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)
open import Data.Sum.Base using (inj₁; inj₂; [_,_])

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

splitArₗ : Ar (ι (n + m)) X → Ar (ι n) X
splitArₗ {n} {m} xs (ι i) = xs (ι (join n m (inj₁ i)))

splitArᵣ : Ar (ι (n + m)) X → Ar (ι m) X
splitArᵣ {n} {m} xs (ι i) = xs (ι (join n m (inj₂ i)))

splitAr : Ar (ι (n + m)) X → Ar (ι n) X × Ar (ι m) X
splitAr xs = ⟨ splitArₗ xs , splitArᵣ xs ⟩

{-
foldr : ∀ {n : ℕ} {X Y : Set} → (X → Y → Y) → Y → Ar (ι n) X → Y
foldr {zero } f acc ar = acc
foldr {suc n} f acc ar = foldr f (f (head₁ ar) acc) (tail₁ ar)

--tail-equality : ∀ 
--  {n : ℕ}
--  {arr₁ arr₂ : Ar (ι (suc n)) X} 
--  → arr₁ ≡ arr₂ 
--  -------------------------
--  → tail₁ arr₁ ≡ tail₁ arr₂

cong-foldr : ∀ 
  {n : ℕ} 
  {X Y : Set}
  {f : X → Y → Y}
  {acc : Y}
  {arr₁ arr₂ : Ar (ι n) X} 
  → arr₁ ≡ arr₂ 
  ------------------------
  → foldr f acc arr₁ ≡ foldr f acc arr₂
cong-foldr {n} {X} {Y} {f} {acc} {arr₁} {.arr₁} refl = refl

foldr-≡ : ∀
  {n : ℕ} 
  {X Y : Set}
  {f : X → Y → Y}
  {g : X → Y → Y}
  {acc : Y}
  {arr : Ar (ι n) X} 
  (prf : ∀ {x : X} {y : Y} → f x y ≡ g x y)
  → foldr {n} f acc arr ≡ foldr {n} g acc arr
foldr-≡ {zero} {X} {Y} {f} {g} {acc} {arr} prf = refl
foldr-≡ {suc n} {g = g} {acc = acc} {arr = arr} prf rewrite 
    prf {arr (ι fzero)} {acc}
  | foldr-≡ {g = g} {g (arr (ι fzero)) acc} {tail₁ arr} prf = refl
-}

zip : Ar (ι n) X → Ar (ι n) Y → Ar (ι n) (X × Y)
zip xs ys pos = ⟨ xs pos , ys pos ⟩

zipWith : (X → Y → Z) → Ar s X → Ar s Y → Ar s Z
zipWith f arr₁ arr₂ pos = f (arr₁ pos) (arr₂ pos)

_++_ : Ar (ι n) X → Ar (ι m) X → Ar (ι (n + m)) X
_++_ {n} {X} {m} arr₁ arr₂ (ι pos) with splitAt n {m} pos
... | inj₁ finN = arr₁ (ι finN)
... | inj₂ finM = arr₂ (ι finM)

iterate : (n : ℕ) → (X → X) → X → Ar (ι n) X
iterate zero    f acc = nil
iterate (suc n) f acc = ι-cons acc (iterate n f (f acc))

-- toFin : Position (ι n) → Fin n
-- toFin (ι x) = x




