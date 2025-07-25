module Matrix where

open import Data.Nat using (ℕ; suc; zero; _+_; _*_)
open import Data.Fin as F using (Fin; join) renaming (zero to fzero; suc to fsuc)
open import Data.Product.Base using (_×_) renaming ( _,_ to ⟨_,_⟩)
open import Data.Sum.Base using (inj₁; inj₂)

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

foldr : ∀ {n : ℕ} {X Y : Set} → (X → Y → Y) → Y → Ar (ι n) X → Y
foldr {zero } f acc ar = acc
foldr {suc n} f acc ar = foldr f (f (head₁ ar) acc) (tail₁ ar)

zip : Ar (ι n) X → Ar (ι n) Y → Ar (ι n) (X × Y)
zip xs ys pos = ⟨ xs pos , ys pos ⟩

zipWith : (X → Y → Z) → Ar s X → Ar s Y → Ar s Z
zipWith f arr₁ arr₂ pos = f (arr₁ pos) (arr₂ pos)

iterate : (n : ℕ) → (X → X) → X → Ar (ι n) X
iterate zero    f acc = nil
iterate (suc n) f acc = ι-cons acc (iterate n f (f acc))

