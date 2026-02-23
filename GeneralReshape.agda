module _ where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong)
open Eq.≡-Reasoning
open import Function
open import Algebra.Definitions

open import Data.Unit
-- This gives a warn on older versions of Agda when Product doesnt have a zipWith method
open import Data.Product hiding (swap; map; map₁; map₂; zipWith)

record Mon : Set₁ where
  field
    U : Set
    El : U → Set

    ε : U
    _●_ : U → U → U

    unit-law : El ε ↔ ⊤
    -- -- The bracketing on the left hand side here is VERY important, otherwise
    -- -- we have a pair where the left is an isomorhism... that took me too long
    pair-law : ∀ a b → El (a ● b) ↔ (El a × El b)

    comm : ∀ a b → a ● b ≡ b ● a

{- 
  Was thinking that it could be nice to use multiple "Levels" of reshape, such
  that we don't add (for example) flat and unflat to the requirements for a 
  module when we dont need them

  Would be nice if we could construct this by pairs of reshapes - i.e. flat and 
  unflat, swap and swap, assocl and assocr - then each module could require only 
  those which it requires
-}
record RShp (S : Set) (P : S → Set) : Set₁ where
  field
    Reshape : S → S → Set
    --_∙_ : ∀ {s p q : S} → Reshape p q → Reshape s p → Reshape s q 
    --_∙_ : ∀ {s p q : S} → RShp.Reshape S P p q → Reshape s p → Reshape s q 
    _⟨_⟩ : ∀ {s p : S} → P s → Reshape p s → P p
    rev : ∀ {s p : S} → Reshape s p → Reshape p s
    rev-eq : ∀ {s p : S} 
            → ∀ (r : Reshape s p) 
            → ∀ (i : P p) 
            →  i ⟨ r ⟩ ⟨ rev r ⟩ ≡ i 
    -- When generalising reshapes, is this always going to hold or does a case 
    -- exist where this is not the case?
    rev-rev : ∀ {s p : S}
            → ∀ (r : Reshape s p)
            → ∀ (i : P p ) → 
            i ⟨ rev (rev r) ⟩ ≡ i ⟨ r ⟩

module A (M : Mon) where
  open Mon M

  infixl 15 _⊗_
  data S : Set where
    ι : U → S  --  ι n means ι (suc n)
    _⊗_ : S → S → S

  variable
    s s′ p q q₁ q₂ r V : S
    m n k : U
    X Y Z : Set

  data P : S → Set where
    ι : El n → P (ι n)
    _⊗_ : P s → P p → P (s ⊗ p)

  Ar : S → Set → Set
  Ar s X = P s → X

  eq-Reshape : S → S → Set
  eq-Reshape s p = s ≡ p

  data eqReshape : S → S → Set where
    eq : eqReshape s s

  eq⟨⟩ : P s → eqReshape s s → P s
  eq⟨⟩ i eq = i

  eqRShp : RShp S P
  eqRShp = record 
    { Reshape = eqReshape
    ; _⟨_⟩ = λ{i eq → i}
    ; rev = λ{eq → eq}
    ; rev-eq = λ{eq i → refl}
    ; rev-rev = λ{eq i → refl}
    }

  data swapReshape : S → S → Set where
    swap : swapReshape (s ⊗ p) (p ⊗ s)

  swap⟨⟩ : P s → swapReshape p s → P p
  swap⟨⟩ (i₁ ⊗ i₂) swap = i₂ ⊗ i₁

  swapRShp : RShp S P
  swapRShp = record 
    { Reshape = swapReshape
    ; _⟨_⟩ = swap⟨⟩
    ; rev = λ{swap → swap}
    ; rev-eq = λ{swap (i₁ ⊗ i₂) → refl}
    ; rev-rev = λ{swap (i₁ ⊗ i₂) → refl}
    }
  
  data assocReshape : S → S → Set where
    assocr : assocReshape ((s ⊗ p) ⊗ q) (s ⊗ (p ⊗ q))
    assocl : assocReshape (s ⊗ (p ⊗ q)) ((s ⊗ p) ⊗ q)


  assoc⟨⟩ : P s → assocReshape p s → P p
  assoc⟨⟩ (ι x) ()
  assoc⟨⟩ ((i₁ ⊗ i₂) ⊗ i₃) assocl = i₁ ⊗ (i₂ ⊗ i₃)
  -- Booky ahhh case
  assoc⟨⟩ (i₁ ⊗ (i₂ ⊗ i₃)) assocr = (i₁ ⊗ i₂) ⊗ i₃
  --assoc⟨⟩ (i₁@(ι _) ⊗ (i₂ ⊗ i₃)) assocr = (i₁ ⊗ i₂) ⊗ i₃
  --assoc⟨⟩ (i₁@(_ ⊗ _) ⊗ (i₂ ⊗ i₃)) assocr = (i₁ ⊗ i₂) ⊗ i₃

  assocRShp : RShp S P
  assocRShp = record 
    { Reshape = assocReshape
    ; _⟨_⟩ = assoc⟨⟩
    ; rev = λ{assocr → assocl; assocl → assocr}
    ; rev-eq = λ{assocr (i₁ ⊗ (i₂ ⊗ i₃)) → ?; assocl ((i₁ ⊗ i₂) ⊗ i₃) → ?}
    ; rev-rev = λ{assoc i → ?}
    }

  {- Don't feel like this is a correct/ possible route...
  concat-RShp : RShp S P → RShp S P → RShp S P
  concat-RShp a b = record
                    { Reshape = ?
                    ; _⟨_⟩ = ?
                    ; rev = ?
                    ; rev-eq = ? 
                    ; rev-rev = ?
                    }
  -}

  {- The idea here is then you can have operations which are guaruntted to work 
     for all reshapes, and others which work for some reshape (such as those 
     which preserve flattening
  -}

  {-
  -- This would of course require me to define flattening...
  PreservesFlattening : (r : RShp S P) → ∀ i → i ⟨ r ⟩ ⟨ flatten ⟩ ≡ i ⟨ flatten ⟩
  -- But would give us a set of reshapes which does not (for example) include swap?
  -}

  {-
  data newReshape : S → S → Set where
    new : newReshape ? ?

  new⟨⟩ : P s → newReshape p s → P p
  new⟨⟩ i new = ?

  newRShp : RShp S P
  newRShp = record 
    { Reshape = newReshape
    ; _⟨_⟩ = new⟨⟩
    ; rev = λ{new → ?}
    ; rev-eq = λ{new i → ?}
    ; rev-rev = λ{new i → ?}
    }
  -}


   



{-
  infixl 5 _∙_
  data Reshape : S → S → Set where
    eq : Reshape s s
    _⊕_ : Reshape s p → Reshape q r → Reshape (s ⊗ q) (p ⊗ r)
    _∙_ : Reshape p q → Reshape s p → Reshape s q
    swap : Reshape (s ⊗ p) (p ⊗ s)
    assocl : Reshape (s ⊗ (p ⊗ q)) ((s ⊗ p) ⊗ q)
    assocr : Reshape ((s ⊗ p) ⊗ q) (s ⊗ (p ⊗ q))
    
    flat   : Reshape (ι n ⊗ ι m) (ι (n ● m))
    unflat : Reshape (ι (n ● m)) (ι n ⊗ ι m)

  _⟨_⟩ : P s → Reshape p s → P p
  i ⟨ eq ⟩ = i
  (i ⊗ i₁) ⟨ r ⊕ r₁ ⟩ = (i ⟨ r ⟩) ⊗ (i₁ ⟨ r₁ ⟩)
  i ⟨ r ∙ r₁ ⟩ = (i ⟨ r ⟩) ⟨ r₁ ⟩
  (i ⊗ i₁) ⟨ swap ⟩ = i₁ ⊗ i
  ((i ⊗ j) ⊗ k) ⟨ assocl ⟩ = i ⊗ (j ⊗ k)
  (i ⊗ (j ⊗ k)) ⟨ assocr ⟩ = (i ⊗ j) ⊗ k
  ι x ⟨ flat ⟩ = let a = (Inverse.to $ pair-law _ _) x 
                 in ι (proj₁ a) ⊗ ι (proj₂ a) 
  (ι x₁ ⊗ ι x₂) ⟨ unflat ⟩ =  ι ((Inverse.from $ pair-law _ _) (x₁ , x₂))

  rev : Reshape s p → Reshape p s
  rev eq = eq
  rev (r₁ ⊕ r₂) = (rev r₁) ⊕ (rev r₂)
  rev (r₁ ∙ r₂) = (rev r₂) ∙ (rev r₁)
  rev swap = swap
  rev assocl = assocr
  rev assocr = assocl
  rev flat = ?
  rev unflat = ?

  rev-rev : ∀ (r : Reshape s p) (i : P p ) → i ⟨ rev (rev r) ⟩ ≡ i ⟨ r ⟩
  rev-rev r i = ?

  rev-eq : ∀ (r : Reshape s p) (i : P p) →  i ⟨ r ∙ rev r ⟩ ≡ i
  rev-eq eq i = refl
  rev-eq (r₁ ⊕ r₂) (i₁ ⊗ i₂) rewrite rev-eq r₁ i₁ | rev-eq r₂ i₂ = refl
  rev-eq (r₁ ∙ r₂) i rewrite rev-eq r₂ (i ⟨ r₁ ⟩) | rev-eq r₁ i  = refl
  rev-eq swap (i₁ ⊗ i₂) = refl
  rev-eq assocl (i₁ ⊗ i₂ ⊗ i₃) = refl
  rev-eq assocr (i₁ ⊗ (i₂ ⊗ i₃)) = refl

  rev-eq′ : ∀ (r : Reshape s p) (i : P s) →  i ⟨ rev r ∙ r ⟩ ≡ i
  rev-eq′ r i rewrite
      sym (rev-rev r (i ⟨ rev r ⟩))
    = rev-eq (rev r) i 

-}
