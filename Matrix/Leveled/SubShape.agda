open import Matrix.Mon

module Matrix.Leveled.SubShape (M : Mon) where
open Mon M

open import Matrix.Leveled.Base M
open import Matrix.Leveled.Reshape M

open import Data.Maybe
open import Data.Product hiding (swap) renaming (map to ×map)

private variable
  l : L

data _⊂_ : S l → S l → Set
data _⊆_ : S l → S l → Set


data _⊆_ where
  id : ∀ {s : S l} → s ⊆ s
  st : ∀ {q s : S l} → q ⊂ s → q ⊆ s

data _⊂_ where
  le : ∀ {q s₁ s₂ : S (ss l)} → q  ⊆ s₁ → q  ⊂ (s₁ ⊗ s₂)
  ri : ∀ {q s₁ s₂ : S (ss l)} → q  ⊆ s₂ → q  ⊂ (s₁ ⊗ s₂)
  bₗ : ∀ {q₁ q₂ s₁ s₂ : S (ss l)} → q₁ ⊂ s₁ → q₂ ⊆ s₂ → (q₁ ⊗ q₂) ⊂ (s₁ ⊗ s₂) 
  bᵣ : ∀ {q₁ q₂ s₁ s₂ : S (ss l)} → q₁ ⊆ s₁ → q₂ ⊂ s₂ → (q₁ ⊗ q₂) ⊂ (s₁ ⊗ s₂)
 
-- I propose that there is some morphism between subshape and reshape 
-- But to make this i need to put it in the context

inv-⊂ : ∀ {q s : S l} → q ⊂ s → S l
inv-⊆ : ∀ {q s : S l} → q ⊆ s → Maybe (S l)

inv-⊆ id = nothing
inv-⊆ (st x) = just (inv-⊂ x)

inv-⊂ (le {s₂ = s₂} s⊆q) = maybe′ (_⊗ s₂) s₂ (inv-⊆ s⊆q)
inv-⊂ (ri {s₁ = s₁} q⊆p) = maybe′ (s₁ ⊗_) s₁ (inv-⊆ q⊆p)
inv-⊂ (bₗ l r) = let ⟦l⟧ = inv-⊂ l in maybe′ (⟦l⟧ ⊗_) ⟦l⟧ (inv-⊆ r)
inv-⊂ (bᵣ l r) = let ⟦r⟧ = inv-⊂ r in maybe′ (_⊗ ⟦r⟧) ⟦r⟧ (inv-⊆ l)

-- This is really ugly -- could be nicer if we could go through normal form
to-resh : ∀ {s q : S (ss l)} → (q⊂s : q ⊂ s) → Reshape s (q ⊗ (inv-⊂ q⊂s)) 
to-resh {l} {a ⊗ b} {.a} (le id) = eq
to-resh {l} {a ⊗ b} {q} (le (st x)) = assoₗ ∙ ((to-resh x) ⊕ eq)
to-resh {l} {a ⊗ b} {.b} (ri id) = swap
to-resh {l} {a ⊗ b} {q} (ri (st x)) = assoₗ ∙ swap ⊕ eq ∙ assoᵣ ∙ (eq ⊕ to-resh x) 
--to-resh {l} {a ⊗ b} {q} (ri (st x)) = (eq ⊕ swap) ∙ assoₗ ∙ (to-resh x ⊕ eq) ∙ swap
to-resh {l} {_ ⊗ _} {.(_ ⊗ _)} (bₗ q⊂s id) = assoᵣ ∙ eq ⊕ swap ∙ assoₗ ∙ (to-resh q⊂s ⊕ eq)
to-resh {l} {_ ⊗ _} {.(_ ⊗ _)} (bₗ q⊂s (st x)) = assoₗ ∙ ((assoᵣ ∙ eq ⊕ swap ∙ assoₗ) ⊕ eq) ∙ assoᵣ ∙  to-resh q⊂s ⊕ to-resh x
to-resh {l} {_ ⊗ _} {.(_ ⊗ _)} (bᵣ id q⊂s) = assoᵣ                     ∙ (eq ⊕ to-resh q⊂s)
to-resh {l} {_ ⊗ _} {.(_ ⊗ _)} (bᵣ (st x) q⊂s) = assoₗ ∙ ((assoᵣ ∙ eq ⊕ swap ∙ assoₗ) ⊕ eq) ∙ assoᵣ ∙ (to-resh x ⊕ to-resh q⊂s)

{-
module _ where
  open import Relation.Binary.PropositionalEquality

  from-resh : ∀ {s q p : S (ss l)} → Reshape s (q ⊗ p) → Σ (q ⊂ s) (λ q⊂s → inv-⊂ q⊂s ≡ p)
  proj₁ (from-resh eq) = le id
  proj₁ (from-resh (r ∙ r₁)) = ?
  proj₁ (from-resh (r ⊕ r₁)) = ?
  proj₁ (from-resh (down r)) = ?
  proj₁ (from-resh swap) = ?
  proj₁ (from-resh assoₗ) = ?
  proj₁ (from-resh assoᵣ) = ?
  proj₂ (from-resh r) = ?


resh-⊆ : ∀ {s s′ q : S (ss l)} → Reshape s s′ → s ⊆ q → s′ ⊆ q
resh-⊆ r id = ?
resh-⊆ r (st x) = ?

resh-⊂ : ∀ {s s′ q : S (ss l)} → Reshape s s′ → s ⊂ q → s′ ⊂ q
resh-⊂ r (le x) = le (?)
resh-⊂ r (ri x) = ?
resh-⊂ r (bₗ s⊂q x) = ?
resh-⊂ r (bᵣ x s⊂q) = ?
-}

-- Ah...
--from : ∀ {s q : S (ss l)} → Reshape s (q ⊗ (inv-⊂ q⊂s)) → q ⊂ s

{-
open import Data.Empty

-- Interesting property...
s⊂s⇒⊥ : ∀ {s : S l} → s ⊂ s → ⊥
s⊂s⇒⊥ (le (st x)) = ?
s⊂s⇒⊥ (ri (st x)) = ?
s⊂s⇒⊥ (bₗ x _) = s⊂s⇒⊥ x
s⊂s⇒⊥ (bᵣ _ x) = s⊂s⇒⊥ x
-}



-- This an idea to try to get arround needing to use asso as much as I have above
-- Define a normal form for all shapes and go through that
{-
--- Defines a normal form for shapes ( NOTE : This is basically lists as its just a tree where every right node is a leaf)
data Normal-Form : S l → Set where
  ν : ∀ (n : U) → Normal-Form (ν n)
  ι : ∀ {s : S l} → Normal-Form s → Normal-Form (ι s)
  _⊗_ : ∀ {s : S (ss l)} {p : S l} → Normal-Form s → Normal-Form p → Normal-Form (s ⊗ (ι p))


--- We can then define a function to take every shape to its normal form
to-NF : (s : S l) → Σ (S l) Normal-Form
to-NF (ν x) = ν x , ν x
to-NF (ι s) = ×map ι ι (to-NF s)
to-NF (s ⊗ (ι p)) =
              let a , b = to-NF s in
              let c , d = to-NF p in 
              (a ⊗ (ι c)) , (b ⊗ d)

open import Relation.Binary.PropositionalEquality

resh : ∀ {s₁ s₂ : S (ss l)} → ((to-NF s₁ .proj₁) ⊗ (to-NF s₂ .proj₁)) ≡ (to-NF (s₁ ⊗ s₂) .proj₁)
resh {l} {ι s₁} {s₂} = ?
resh {l} {s₁ ⊗ s₃} {s₂} = ?

to-NFᵣ : ∀ {s : S l} → Reshape s (to-NF s .proj₁)
to-NFᵣ {.zz} {ν x} = eq
to-NFᵣ {.(ss _)} {ι s} = down (up to-NFᵣ)
to-NFᵣ {.(ss _)} {s ⊗ ι s₁} = to-NFᵣ ⊕ to-NFᵣ
to-NFᵣ {.(ss _)} {s ⊗ (s₁ ⊗ s₂)} = ? ∙ to-NFᵣ ⊕ to-NFᵣ
-}




