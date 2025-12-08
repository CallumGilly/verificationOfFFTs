module Matrix.Reshape where

open import Data.Nat using (ℕ; _*_; NonZero)
open import Data.Nat.Properties using (*-comm; *-assoc)
open import Data.Fin as F using (Fin; combine; remQuot; quotRem; toℕ; cast)
open import Data.Fin.Properties using (remQuot-combine; combine-remQuot; cast-is-id; cast-trans)

open import Data.Product using (_,_; proj₁; proj₂)
open import Matrix using (Shape; Position; Ar; ι; _⊗_; length)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; subst; sym)
open Eq.≡-Reasoning

variable
  m n k : ℕ
  s p q r : Shape
  X Y Z : Set

infixr 5 _∙_
infixl 10 _⊕_

----------------------------
--- Language of reshapes ---
----------------------------

data Reshape : Shape → Shape → Set where
  eq     : Reshape s s
  _∙_    : Reshape p q → Reshape s p → Reshape s q
  _⊕_    : Reshape s p → Reshape q r → Reshape (s ⊗ q) (p ⊗ r)
  split  : Reshape (ι (m * n)) (ι m ⊗ ι n)
  flat   : Reshape (ι m ⊗ ι n) (ι (m * n))
  swap   : Reshape (s ⊗ p) (p ⊗ s)
  assoₗ  : Reshape ((s ⊗ p) ⊗ q) (s ⊗ (p ⊗ q))
  assoᵣ  : Reshape (s ⊗ (p ⊗ q)) ((s ⊗ p) ⊗ q)

--------------------------------------------
--- Application of Reshapes to Positions ---
--------------------------------------------

_⟨_⟩ : Position p → Reshape s p → Position s
i             ⟨ eq     ⟩ = i
i             ⟨ r ∙ r₁ ⟩ = i ⟨ r ⟩ ⟨ r₁ ⟩
(i ⊗ j)       ⟨ r ⊕ r₁ ⟩ = (i ⟨ r ⟩) ⊗ (j ⟨ r₁ ⟩)
(ι i ⊗ ι j)   ⟨ split  ⟩ = ι (combine i j)
ι i           ⟨ flat   ⟩ = let a , b = remQuot _ i in ι a ⊗ ι b
(i ⊗ j)       ⟨ swap   ⟩ = j ⊗ i
(i ⊗ (j ⊗ k)) ⟨ assoₗ  ⟩ = (i ⊗ j) ⊗ k
((i ⊗ j) ⊗ k) ⟨ assoᵣ  ⟩ = i ⊗ (j ⊗ k)

------------------------------------------
--- Application of Reshape to Matrix's ---
------------------------------------------

reshape : Reshape s p → Ar s X → Ar p X
reshape r a ix = a (ix ⟨ r ⟩ )

---------------------------------------------
--- The reverse of each Reshape operation ---
---------------------------------------------

rev : Reshape s p → Reshape p s
rev eq = eq
rev (r ⊕ r₁) = rev r ⊕ rev r₁
rev (r ∙ r₁) = rev r₁ ∙ rev r
rev split = flat
rev flat = split
rev swap = swap
rev assoₗ = assoᵣ
rev assoᵣ = assoₗ

--- Properties of reverse
rev-eq : 
  ∀ (r : Reshape s p) 
    (i : Position p ) 
  ---------------------
  → i ⟨ r ∙ rev r ⟩ ≡ i
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
rev-eq assoₗ (i ⊗ (j ⊗ k)) = refl
rev-eq assoᵣ ((i ⊗ j) ⊗ k) = refl

rev-rev : 
  ∀ (r : Reshape s p) 
    (i : Position p )
  -----------------------------
  → i ⟨ rev (rev r) ⟩ ≡ i ⟨ r ⟩
rev-rev eq i = refl
rev-rev (r ∙ r₁) i rewrite rev-rev r (i) | rev-rev r₁ (i ⟨ r ⟩) = refl
rev-rev (r ⊕ r₁) (i ⊗ i₁) rewrite rev-rev r i | rev-rev r₁ i₁ = refl
rev-rev split i = refl
rev-rev flat i = refl
rev-rev swap i = refl
rev-rev assoₗ (i ⊗ (j ⊗  k)) = refl
rev-rev assoᵣ ((i ⊗ j) ⊗ k) = refl

--------------------------------------------------------------------
--- Transposition of Shapes, and the relating Reshape operations ---
--------------------------------------------------------------------

transpose : Shape → Shape
transpose (ι x   ) = (ι x)
transpose (s ⊗ s₁) = s₁ ⊗ s

transposeᵣ : Reshape s (transpose s)
transposeᵣ {ι x   } = eq
transposeᵣ {s ⊗ s₁} = swap

transp-inv : transpose (transpose s) ≡ s
transp-inv {ι x   } = refl
transp-inv {s ⊗ s₁} = refl

------------------------------------------------------------------------------
--- Recursive transposition of Shapes, and the relating Reshape operations ---
------------------------------------------------------------------------------

recursive-transpose : Shape → Shape
recursive-transpose (ι x   ) = ι x
recursive-transpose (s ⊗ s₁) = recursive-transpose s₁ ⊗ recursive-transpose s

recursive-transposeᵣ : Reshape s (recursive-transpose s)
recursive-transposeᵣ {ι x   } = eq
recursive-transposeᵣ {s ⊗ s₁} = swap ∙ recursive-transposeᵣ ⊕ recursive-transposeᵣ

recursive-transpose-inv : recursive-transpose (recursive-transpose s) ≡ s
recursive-transpose-inv {ι x   } = refl
recursive-transpose-inv {s ⊗ s₁} rewrite recursive-transpose-inv {s} | recursive-transpose-inv {s₁} = refl

--- The cardinality of a shape, and the cardinality of its recursive transposition are equal
|s|≡|sᵗ| : length s ≡ length (recursive-transpose s)
|s|≡|sᵗ| {ι x} = refl
|s|≡|sᵗ| {s ⊗ r} rewrite
    *-comm (length s) (length r)
  | |s|≡|sᵗ| {s} 
  | |s|≡|sᵗ| {r} 
  = refl

-----------------------------
--- Flatten and unflatten ---
-----------------------------
-- Used to go from an n dimensional Matrix, to a Vector

♭ : Reshape s (ι (length s))
♭ {ι x   } = eq
♭ {s ⊗ s₁} = flat ∙ ♭ ⊕ ♭

-- Unflatten is free from flatten
♯ : Reshape (ι (length s)) s
♯ = rev ♭

---------------
--- Reindex ---
---------------
-- Used to allow comparison between flattened Matricies of different original shapes

reindex : m ≡ n → Reshape (ι m) (ι n)
reindex {m} {n} prf = subst (λ t → Reshape (ι m) (ι t)) prf eq

--- Reindex Properties ---
reindex-cast : 
    (prf : n ≡ m) 
  → ∀ (i : Fin m) 
  ------------------------------------------------
  → (ι i ⟨ reindex prf ⟩) ≡ (ι (cast (sym prf) i))
reindex-cast {n} {m} refl i = cong ι (sym (cast-is-id refl i))

ext : 
  ∀ (arr : Ar (ι m) X) 
  → (prf : m ≡ n) 
  → ∀ (i : Position (ι n))  
  ------------------------------------------------------------------
  → subst (λ s → Ar (ι s) X) prf arr i ≡ reshape (reindex prf) arr i
ext arr refl (ι x) = refl

reindex-reindex : 
    (prf : m ≡ n) 
  → ∀ (i : Position (ι m)) 
  -------------------------------------------
  → i ⟨ reindex (sym prf) ∙ reindex prf ⟩ ≡ i
reindex-reindex refl i = refl

-----------------------
--- Reindex flatten ---
-----------------------

flatten-reindex : Reshape s (ι (length (recursive-transpose s)))
flatten-reindex {s} = reindex (|s|≡|sᵗ| {s}) ∙ ♭

