module src.Reshape where

open import Data.Nat
open import Data.Nat.Properties using (*-comm; *-zeroʳ)
open import Data.Fin as F using (Fin; combine; remQuot; quotRem; toℕ; cast)
open import Data.Fin.Properties using (remQuot-combine; combine-remQuot; cast-is-id; cast-trans)

open import Data.Product using (Σ; ∃; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
open import src.Matrix using (Shape; Position; Ar; ι; _⊗_; length)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans)
open Eq.≡-Reasoning

open import src.Extensionality using (extensionality)

open import Function.Base using (_$_; id; _∘_)

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
--  comm-eq : m ≡ n → Reshape (ι n) (ι m)
--  reindex : Reshape (ι (m * n)) (ι (n * m))
--comm-eq {n} {m} rewrite *-comm m n = eq

-- For all shapes s and p
_⟨_⟩ : ∀ {s p : Shape} → Position p → Reshape s p → Position s
i           ⟨ eq     ⟩ = i
i           ⟨ r ∙ r₁ ⟩ = i ⟨ r ⟩ ⟨ r₁ ⟩
(i ⊗ j)     ⟨ r ⊕ r₁ ⟩ = (i ⟨ r ⟩) ⊗ (j ⟨ r₁ ⟩)
(ι i ⊗ ι j) ⟨ split  ⟩ = ι (combine i j)
ι i         ⟨ flat   ⟩ = let a , b = remQuot _ i in ι a ⊗ ι b
(i ⊗ j)     ⟨ swap   ⟩ = j ⊗ i
--ι i         ⟨ comm-eq prf ⟩ = ι (cast prf i) 
--ι i ⟨ reindex {m} {n} ⟩ = ι (cast (*-comm n m) i)


--cong-eq : ∀ {n m : ℕ} → n ≡ m → eq {?} ≡ eq

reshape : Reshape s p → Ar s X → Ar p X
reshape r a ix = a (ix ⟨ r ⟩ )

rev : Reshape s p → Reshape p s
rev eq = eq
rev (r ⊕ r₁) = rev r ⊕ rev r₁
rev (r ∙ r₁) = rev r₁ ∙ rev r
rev split = flat
rev flat = split
rev swap = swap
--rev (comm-eq refl) = comm-eq refl
--rev (reindex {m} {n}) = reindex {n} {m}

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
--rev-eq (comm-eq refl) (ι i) rewrite 
--    cast-is-id refl i 
--  | cast-is-id refl i = refl
--rev-eq (reindex {m} {n}) (ι i) rewrite 
--    cast-trans (*-comm n m) (*-comm m n) i 
--  | cast-is-id refl i = refl

eq+eq : ∀ {X : Set} {n m : ℕ} (arr : Ar (ι n ⊗ ι m) X) → reshape (eq ⊕ eq) arr ≡ arr
eq+eq {X} {n} {m} arr = extensionality λ{(ι x ⊗ ι y) → refl }

eq+eq-position-wrapper : ∀ {X : Set} {n m : ℕ} (arr : Ar (ι n ⊗ ι m) X) (pos : Position (ι n ⊗ ι m)) → arr (pos ⟨ eq ⊕ eq ⟩) ≡ arr pos
eq+eq-position-wrapper arr (ι x ⊗ ι y) = refl

rev-rev : (r : Reshape s p) → ∀ (i : Position p) → i ⟨ rev (rev r) ⟩ ≡ i ⟨ r ⟩
rev-rev eq i = refl
rev-rev (r ∙ r₁) i rewrite rev-rev r (i) | rev-rev r₁ (i ⟨ r ⟩) = refl
rev-rev (r ⊕ r₁) (i ⊗ i₁) rewrite rev-rev r i | rev-rev r₁ i₁ = refl
rev-rev split i = refl
rev-rev flat i = refl
rev-rev swap i = refl
--rev-rev (comm-eq refl) i = refl
--rev-rev reindex i = refl

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

-- Define flatten - This is legthin in matrix
-- flatten : Shape → ℕ
-- flatten (ι x) = x
-- flatten (s ⊗ s₁) = flatten s * flatten s₁
_♭ : Reshape s (ι (length s))
_♭ {ι x} = eq
_♭ {s ⊗ s₁} = flat ∙ _♭ ⊕ _♭

-- Get unflatten for free
_♯ : Reshape (ι (length s)) s
_♯ = rev _♭

reindex : m ≡ n → Reshape (ι m) (ι n)
reindex {m} {n} prf = subst (λ t → Reshape (ι m) (ι t)) prf eq

reindex-cast : (prf : n ≡ m) → (i : Fin m) → (ι i ⟨ reindex prf ⟩) ≡ (ι (cast (sym prf) i))
reindex-cast {n} {m} refl i = cong ι (sym (cast-is-id refl i))

ext : (arr : Ar (ι m) X) → (prf : m ≡ n) → ∀ i → subst (λ s → Ar (ι s) X) prf arr i ≡ reshape (reindex prf) arr i
ext arr refl (ι x) = refl

|s|≡|sᵗ| : length s ≡ length (recursive-transpose s)
|s|≡|sᵗ| {ι x} = refl
|s|≡|sᵗ| {s ⊗ r} rewrite
    *-comm (length s) (length r)
  | |s|≡|sᵗ| {s} 
  | |s|≡|sᵗ| {r} 
  = refl

flatten-reindex : Reshape s (ι (length (recursive-transpose s)))
flatten-reindex {s} = reindex (|s|≡|sᵗ| {s}) ∙ _♭

--_♭₂ : Reshape (s) (ι (length (recursive-transpose s)))
--_♭₂ {ι x} = eq
--_♭₂ {s ⊗ s₁} = comm-eq (*-comm (length (recursive-transpose s₁)) (length (recursive-transpose s))) ∙ flat ∙ _♭₂ ⊕ _♭₂

-- _♭₃ : Reshape (s) (ι (length (recursive-transpose s)))
-- _♭₃ {ι x} = eq
-- _♭₃ {s ⊗ s₁} = (reindex {length (recursive-transpose s)} {length (recursive-transpose s₁)}) ∙ flat ∙ _♭₃ ⊕ _♭₃

            -- (ι
            --  (length (recursive-transpose s) * length (recursive-transpose s₁)))
            -- (ι
            --  (length (recursive-transpose s₁) * length (recursive-transpose s)))
--_♭₂ {s ⊗ s₁} = comm-eq {length (recursive-transpose s)} {length (recursive-transpose s₁)} ∙ flat ∙ _♭₂ ⊕ _♭₂
--_♯₂ {s ⊗ s₁} = (_♯₂ {s₁} ⊕ _♯₂ {s}) ∙ split₂ {length (recursive-transpose s₁)} {length ?}
--_♯₂ {ι x} = eq
--_♯₂ {s ⊗ s₁} with (lemma₁ {s ⊗ s₁})
--... | tmp = ? ∙ split {length s₁} {length s} 
--_♯₂ {s ⊗ s₁} with (lemma₁ {s}) | (lemma₁ {s₁})
--... | tmp | tmp₁ = ? ∙ split {length s₁} {length s} 
--_♯₂ {s} rewrite lemma₁ {s} = _♯



--_♯₂ {ι x} = _♯ 
--_♯₂ {s ⊗ s₁} = ? ∙ split {length s} {length s}
  --where
  --  helper : length s * length s₁ ≡ length s₁ * length s → Reshape (ι (length s)) (recursive-transpose s)
  --  helper x = ? ∙ split {length s} {length s₁}
--_♯₂ {s ⊗ s₁} = (_♯₂ ⊕ _♯₂) ∙ swap ∙ split 

--length-invariance : 
--    ∀ {s q : Shape} 
--  → Reshape s q
--  → length s ≡ length q
--length-invariance {s} {.s} eq = refl
--length-invariance {s} {q} (r ∙ r₁) rewrite length-invariance r₁ | length-invariance r = refl
--length-invariance {.(_ ⊗ _)} {.(_ ⊗ _)} (r ⊕ r₁) rewrite length-invariance r | length-invariance r₁ = refl
--length-invariance {s} {q} split = refl
--length-invariance {s} {q} flat = refl
--length-invariance {.(s ⊗ p)} {.(p ⊗ s)} (swap {s} {p}) rewrite *-comm (length s) (length p) = refl




