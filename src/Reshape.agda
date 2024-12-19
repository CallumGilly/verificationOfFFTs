module src.Reshape where

open import Data.Nat
open import Data.Fin as F using (Fin; combine; remQuot; quotRem; toℕ)
open import Data.Fin.Properties using (remQuot-combine; combine-remQuot)

open import Data.Product using (Σ; ∃; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
open import src.Matrix using (Shape; Position; Ar; ι; _⊗_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning


variable
  m n k : ℕ
  s p q r : Shape
  X Y Z : Set

infixr 5 _∙_
infixl 10 _⊕_
data Reshape : Shape → Shape → Set where
  eq     : Reshape s s
  _∙_    : Reshape p q → Reshape s p → Reshape s q
  _⊕_    : Reshape s p → Reshape q r → Reshape (s ⊗ q) (p ⊗ r)
  split  : Reshape (ι (m * n)) (ι m ⊗ ι n)
  flat   : Reshape (ι m ⊗ ι n) (ι (m * n))
  swap   : Reshape (s ⊗ p) (p ⊗ s)

-- For all shapes s and p
_⟨_⟩ : ∀ {s p : Shape} → Position p → Reshape s p → Position s
i           ⟨ eq     ⟩ = i
i           ⟨ r ∙ r₁ ⟩ = i ⟨ r ⟩ ⟨ r₁ ⟩
(i ⊗ j)     ⟨ r ⊕ r₁ ⟩ = (i ⟨ r ⟩) ⊗ (j ⟨ r₁ ⟩)
(ι i ⊗ ι j) ⟨ split  ⟩ = ι (combine i j)
ι i         ⟨ flat   ⟩ = let a , b = remQuot _ i in ι a ⊗ ι b
(i ⊗ j)     ⟨ swap   ⟩ = j ⊗ i

reshape : Reshape s p → Ar s X → Ar p X
reshape r a ix = a (ix ⟨ r ⟩ )

rev : Reshape s p → Reshape p s
rev eq = eq
rev (r ⊕ r₁) = rev r ⊕ rev r₁
rev (r ∙ r₁) = rev r₁ ∙ rev r
rev split = flat
rev flat = split
rev swap = swap

-- Reverse properties
rev-eq : (r : Reshape s p) → ∀ (i : Position p) → i ⟨ r ∙ rev r ⟩ ≡ i
rev-eq eq i = refl
rev-eq (r ∙ r₁) i rewrite rev-eq r₁ (i ⟨ r ⟩) = rev-eq r i
rev-eq (r ⊕ r₁) (i ⊗ i₁) rewrite rev-eq r₁ i₁ | rev-eq r i = refl
rev-eq (split {m = m} {n = n}) (ι x ⊗ ι x₁) with cong proj₁ (remQuot-combine x x₁) | cong proj₂ (remQuot-combine x x₁)
... | fst | snd = 
  begin
    (ι (proj₂ (quotRem n (combine x x₁))) ⊗ ι (proj₁ (quotRem {m} n (combine x x₁))))
  ≡⟨ cong (ι (proj₂ (quotRem n (combine x x₁))) ⊗_) (cong ι snd) ⟩
    (ι (proj₂ (quotRem n (combine x x₁))) ⊗ ι x₁)
  ≡⟨ cong (_⊗ ι x₁) (cong ι fst)⟩
    (ι x ⊗ ι x₁)
  ∎
rev-eq (flat {m = m} {n = n}) (ι x) rewrite combine-remQuot {m} n x = refl 
rev-eq swap (i ⊗ i₁) = refl

rev-rev : (r : Reshape s p) → ∀ (i : Position p) → i ⟨ rev (rev r) ⟩ ≡ i ⟨ r ⟩
rev-rev eq i = refl
rev-rev (r ∙ r₁) i rewrite rev-rev r (i) | rev-rev r₁ (i ⟨ r ⟩) = refl
rev-rev (r ⊕ r₁) (i ⊗ i₁) rewrite rev-rev r i | rev-rev r₁ i₁ = refl
rev-rev split i = refl
rev-rev flat i = refl
rev-rev swap i = refl

-- Define transpose
transpose : Shape → Shape
transpose (ι x) = (ι x)
transpose (s ⊗ s₁) = s₁ ⊗ s
transposeᵣ : Reshape s (transpose s)
transposeᵣ {ι x} = eq
transposeᵣ {s ⊗ s₁} = swap
transp-inv : ∀ {s : Shape} → transpose (transpose s) ≡ s
transp-inv {ι x} = refl
transp-inv {s ⊗ s₁} = refl

recursive-transpose : Shape → Shape
recursive-transpose (ι x) = ι x
recursive-transpose (s ⊗ s₁) = recursive-transpose s₁ ⊗ recursive-transpose s
recursive-transposeᵣ : Reshape s (recursive-transpose s)
recursive-transposeᵣ {ι x} = eq
recursive-transposeᵣ {s ⊗ s₁} = swap ∙ recursive-transposeᵣ ⊕ recursive-transposeᵣ
recursive-transpose-inv : ∀ {s : Shape} → recursive-transpose (recursive-transpose s) ≡ s
recursive-transpose-inv {ι x} = refl
recursive-transpose-inv {s ⊗ s₁} rewrite recursive-transpose-inv {s} | recursive-transpose-inv {s₁} = refl

-- Define flatten
flatten : Shape → ℕ
flatten (ι x) = x
flatten (s ⊗ s₁) = flatten s * flatten s₁
_♭ : Reshape s (ι (flatten s))
_♭ {ι x} = eq
_♭ {s ⊗ s₁} = flat ∙ _♭ ⊕ _♭

-- Get unflatten for free
_♯ : Reshape (ι (flatten s)) s
_♯ = rev _♭
