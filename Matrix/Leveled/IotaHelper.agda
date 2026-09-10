{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --without-K #-}

open import Matrix.Mon

module Matrix.Leveled.IotaHelper (M : Mon) where
  open Mon M
  open import Matrix.Leveled.Base M
  open import Matrix.Leveled.Reshape M

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
  open Eq.≡-Reasoning
  open import Function
  open import Algebra.Definitions
  open import Data.Product hiding (map; swap)
  open import Data.Product.Properties

  private
    infixl 4 _⊡_
    _⊡_ = trans

    variable
      ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ l r w : L
      s s′ : S ℓ
      u : U
      X : Set

  module _ where
    open import Data.Maybe renaming (_>>=_ to _⟫=_; zip to zipM) 

    data InplaceReshape : {s : S ℓ} {s′ : S ℓ′} → Reshape s s′ → Set where
      eq     : ∀ {s  : S ℓ } → InplaceReshape {_} {_} {s} {s} eq
      _∙_    : ∀ {s₁ : S ℓ₁} {s₂ : S ℓ₂} {s₃ : S ℓ₃}     {r₁ : Reshape s₁ s₂} {r₂ : Reshape s₂ s₃} → InplaceReshape r₂ → InplaceReshape r₁ → InplaceReshape (r₂ ∙ r₁)
      _⊕_    : ∀ {s₁ s₂ : S (ss ℓ₁)} {s₃ s₄ : S (ss ℓ₂)} {r₁ : Reshape s₁ s₃} {r₂ : Reshape s₂ s₄} → InplaceReshape r₁ → InplaceReshape r₂ → InplaceReshape (r₁ ⊕ r₂)
      up     : ∀ {r : Reshape s s′} → InplaceReshape r → InplaceReshape (up r)
      down   : ∀ {r : Reshape s s′} → InplaceReshape r → InplaceReshape (down r)
      assoₗ  : ∀ {s₁ s₂ s₃ : S (ss ℓ)} → InplaceReshape (assoₗ {ℓ} {s₁} {s₂} {s₃})
      assoᵣ  : ∀ {s₁ s₂ s₃ : S (ss ℓ)} → InplaceReshape (assoᵣ {ℓ} {s₁} {s₂} {s₃})
      flat   : ∀ {n m : U} → InplaceReshape (flat {n} {m})
      unflat : ∀ {n m : U} → InplaceReshape (unflat {n} {m})

    Inplace-rev : ∀ {s : S ℓ} {s′ : S ℓ′} → ∀ (r : Reshape s s′) → InplaceReshape r → InplaceReshape (rev r)
    Inplace-rev = ?

    isInplace : ∀ {s : S ℓ} {s′ : S ℓ′} → (r : Reshape s s′) → Maybe (InplaceReshape r)
    isInplace eq        = just eq
    isInplace (r₁ ∙ r₂) = zipM (isInplace r₁) (isInplace r₂) ⟫= uncurry (just ∘₂′ _∙_) 
    isInplace (r₁ ⊕ r₂) = zipM (isInplace r₁) (isInplace r₂) ⟫= uncurry (just ∘₂′ _⊕_)
    isInplace (up   r)  = isInplace r ⟫= just ∘ up
    isInplace (down r)  = isInplace r ⟫= just ∘ down
    isInplace flat      = just flat
    isInplace unflat    = just unflat
    isInplace swap      = nothing
    isInplace assoₗ     = just assoₗ
    isInplace assoᵣ     = just assoᵣ
  

    open import Data.Unit
    open import Data.Empty

    isJust : ∀ {A : Set} → Maybe A → Set
    isJust nothing = ⊥
    isJust (just x) = ⊤
    
    fromJust : ∀ {A} → (x : Maybe A) → isJust x → A
    fromJust (just x) tt = x


    u-flat-id-isInplace : ∀ {s₁} → InplaceReshape (u-flatten-z-id {s₁})
    u-flat-id-isInplace {ν x} = eq

    -- It's very annoying that reshapes constructed from splitting on the shape apparently cannot use the fromJust isInplace "Tactic"
    flatten-z-isInplace : {s : S (ss ℓ)} → InplaceReshape (flatten-zᵣ {_} {s})
    flatten-z-isInplace {s = s} = ?
    {-
    flatten-z-isInplace {zz} {ι s} = down eq
    flatten-z-isInplace {zz} {s₁ ⊗ s₂} = flat ∙ ((up u-flat-id-isInplace ∙ flatten-z-isInplace) ⊕ (up u-flat-id-isInplace ∙ flatten-z-isInplace))
    flatten-z-isInplace {ss ℓ} {ι s} = down eq
    flatten-z-isInplace {ss ℓ} {s ⊗ s₁} = flatten-z-isInplace ⊕ flatten-z-isInplace
    -}

    
  {-
  For the DFT≡FFT proofs, we need to prove equality over iota ALLOT, the 
  theory I had here was as follows:
    - iota (i ⟨ r₁ ⟩) ≡ iota i whenever r₁ does not not contain any swaps (semi-decision)
    - All such reshapes are predicated on by InplaceReshape, which we can automatically produce an instance for with isInplace
    - If I can prove this property for all reshapes r which are inplace, we can make a tactic to make iota proofs automatic
    - Profit

    - Unfortunatly, this does not seem as easy as I hoped

  -}
  
  {-
  module _ where
    open import Function
    private variable
      p₁ p₂ : S ℓ
      n : U

    data FlatShape : {ℓ : L} → S ℓ → Set where  
      ν : ∀ (n : U) → FlatShape (ν n)
      ι : ∀ {s : S ℓ} → FlatShape s → FlatShape (ι s)

    inp-flat : ∀ {r₁ : Reshape p₁ s} 
           → FlatShape p₁
           → InplaceReshape r₁
           → FlatShape s
    inp-flat {n} ♭ eq = ♭
    inp-flat ♭ (a ∙ b) = inp-flat (inp-flat ♭ b) a
    inp-flat ♭ (up x) = ι (inp-flat ♭ x)
    inp-flat (ι ♭) (down x) = inp-flat ♭ x
    inp-flat (ν n) x₁ = ?

    inp-flat′ : ∀ {r₁ : Reshape p₁ s} 
           → FlatShape s
           → InplaceReshape r₁
           → FlatShape p₁
    inp-flat′ {n} ♭ eq = ♭
    inp-flat′ ♭ (b ∙ a) = inp-flat′ (inp-flat′ ♭ b) a
    inp-flat′ (ι ♭) (up x) = inp-flat′ ♭ x
    inp-flat′ ♭ (down x) = ι (inp-flat′ ♭ x)
    inp-flat′ (ν n) flat = ?

    iota-♭ : ∀ {s : S ℓ} → FlatShape s → Ar s U
    iota-♭ (ν n) = iota ∘ ι 
    iota-♭ (ι f) (ι i) = iota-♭ f i

    iota≡iota-♭ : ∀ (i : P (ι (ν n)))
               → iota i ≡ iota-♭ (ι (ν n)) i
    iota≡iota-♭ (ι (ν x)) = refl

    lemma₃ : ∀ {r₁ : Reshape s′ s} 
           → (♭ : FlatShape s)
           → (inp : InplaceReshape r₁)
           → ∀ (i : P s)
           → iota-♭ (inp-flat′ ♭ inp) (i ⟨ r₁ ⟩) ≡ iota-♭ ♭ i
    lemma₃ ♭ eq i = refl
    lemma₃ ♭ (_∙_ {r₁ = r₁} {r₂} inp inp₁) i = lemma₃ (inp-flat′ ♭ inp) inp₁ (i ⟨ r₂ ⟩) ⊡ lemma₃ ♭ inp i
    lemma₃ (ι ♭) (up inp) (ι i) = lemma₃ ♭ inp i
    lemma₃ ♭ (down inp) i = lemma₃ ♭ inp i
    lemma₃ ♭ a@flat i with inp-flat′ ♭ a
    ... | ()

    helper₁ : {r₁ : Reshape (ι (ν n)) (ι (ν n))}
              (x : InplaceReshape r₁) (i : P (ι (ν n))) →
              iota-♭ (ι (ν n)) (i ⟨ r₁ ⟩) ≡
              iota-♭ (inp-flat′ (ι (ν n)) x) (i ⟨ r₁ ⟩)
    helper₁ {n} {r₁} x i with inp-flat′ (ι (ν n)) x
    ... | ι (ν .n) = refl

    -- THIS IS ONLY USEFUL IF ITS Reshape (ι (ν n)) s !!
    lemma₂ : ∀ {r₁ : Reshape (ι (ν n)) (ι (ν n))} 
           → InplaceReshape r₁
           → ∀ (i : P (ι (ν n)))
           → iota (i ⟨ r₁ ⟩) ≡ iota i
    lemma₂ {n} {r₁} x i with inp-flat′ (ι (ν n)) x
    ... | ι (ν n) = iota≡iota-♭ (i ⟨ r₁ ⟩) 
                   ⊡ helper₁ {_} {_} x i 
                   ⊡ lemma₃ (ι (ν n)) x i
                   ⊡ (sym (iota≡iota-♭ i))
     -}

    {-
    inplaceReshape→iota≡ : ∀ {r₁ : Reshape (ι (ν n)) s} 
                         → ∀ {r₂ : Reshape (ι (ν n)) s} 
                         → InplaceReshape r₁
                         → InplaceReshape r₂
                         → ∀ (i : P s)
                         → iota (i ⟨ r₁ ⟩) ≡ iota (i ⟨ r₂ ⟩)
    inplaceReshape→iota≡ {n} {.(ss zz)} {.(ι (ν n))} {r₁} {.eq} inp₁ eq i = lemma₂ inp₁ i
    inplaceReshape→iota≡ {n} {ℓ} {s} {r₁} {.(_ ∙ _)} inp₁ (inp₂ ∙ inp₃) i = ?
    inplaceReshape→iota≡ {n} {.(ss _)} {.(ι _)} {r₁} {.(up _)} inp₁ (up inp₂) (ι i) = ?
    inplaceReshape→iota≡ {n} {ℓ} {s} {r₁} {.(down _)} inp₁ (down inp₂) i = ?
    -}
    open Inverse

    lem₁ : ∀ {s q : S ℓ} → length s ≡ length q → u-flatten s ≡ u-flatten q
    lem₁ {.zz} {ν x₁} {ν x₂} x = x
    lem₁ {.(ss _)} {ι s} {ι q} x = lem₁ {_} {s} {q} x 
    lem₁ {.(ss _)} {ι s} {q₁ ⊗ q₂} x = ?
    lem₁ {.(ss _)} {s ⊗ s₁} {q} x = ?

    mutual
    lem₂ : ∀ {s₁ p₁ : S ℓ} {s₂ p₂ : S ℓ′} {r₁ : Reshape s₁ s₂} {r₂ : Reshape p₁ p₂}
        → InplaceReshape r₁
        → InplaceReshape r₂
        → ∀ {i₁ : P s₂}
        → ∀ {i₂ : P p₂}
        → iota′ ((ι ((i₁ ⟨ r₁ ⟩) ⟨ rev ν-flattenᵣ ⟩) ⊗ ι ((i₂ ⟨ r₂ ⟩) ⟨ rev ν-flattenᵣ ⟩)) ⟨ unflat ⟩)
        ≡ iota′ ((i₁ ⟨ r₁ ⟩) ⟨ rev ν-flattenᵣ ⟩) ● iota′ ((i₂ ⟨ r₂ ⟩) ⟨ rev ν-flattenᵣ ⟩)
    lem₂ {ℓ} {ℓ′} {s₁} {p₁} {s₂} {p₂} {r₁} {r₂} inp₁ inp₂ {i₁} {i₂} with (i₁ ⟨ r₁ ⟩) ⟨ rev ν-flattenᵣ ⟩ | (i₂ ⟨ r₂ ⟩) ⟨ rev ν-flattenᵣ ⟩
    ... | ν x | ν y = ?

    thm₁ : ∀ {s : S ℓ} {s′ : S ℓ′}
         → ∀ (r : Reshape s′ s)
         → InplaceReshape r
         → (i : P s) → iota′ (i ⟨ r ⟩ ⟨ rev ν-flattenᵣ ⟩) ≡ iota′ (i ⟨ rev ν-flattenᵣ ⟩)
    thm₁ eq eq i = refl
    thm₁ (r₁ ∙ r₂) (x₁ ∙ x₂) i = thm₁ r₂ x₂ (i ⟨ r₁ ⟩) ⊡ thm₁ r₁ x₁ i
    thm₁ (_⊕_ {s = s} {p} {q} {t} r₁ r₂) (x₁ ⊕ x₂) (i₁ ⊗ i₂) with sym (resh-u-flatten r₁) | sym (resh-u-flatten r₂)
    thm₁ (_⊕_ {s = s} {p} {q} {t} r₁ r₂) (x₁ ⊕ x₂) (i₁ ⊗ i₂) | a | b = ?
      {-
          cong 
            --{} 
            --{} 
            iota′ 
            {((ι ((i₁ ⟨ r₁ ⟩) ⟨ rev ν-flattenᵣ ⟩) ⊗ ι ((i₂ ⟨ r₂ ⟩) ⟨ rev ν-flattenᵣ ⟩)) ⟨ unflat ⟩)}
            {let x = ((ι (i₁ ⟨ rev ν-flattenᵣ ⟩) ⊗ ι (i₂ ⟨ rev ν-flattenᵣ ⟩)) ⟨ unflat ⟩) in 
             let y = subst P (cong ν (cong₂ _●_ a b)) x in 
             let z = ((ι (i₁ ⟨ rev ν-flattenᵣ ⟩) ⊗ ι (i₂ ⟨ rev ν-flattenᵣ ⟩)) ⟨ unflat ⟩) in ? }
            ?
        -}
    thm₁ (up r) (up x) (ι i) = thm₁ r x i
    thm₁ (down r) (down x) i = thm₁ r x i
    thm₁ (flat {m} {n}) flat (ν x) = cong toU ( inverse (pair-law m n) .proj₂ refl )
    thm₁ unflat unflat (ι i ⊗ ι j) = refl
    thm₁ swap () i
    thm₁ {ss ℓ} {ss ℓ′} {s₁ ⊗ (s₂ ⊗ s₃)} {(.s₁ ⊗ .s₂) ⊗ .s₃} assoₗ assoₗ (i₁ ⊗ (i₂ ⊗ i₃)) = ?
    thm₁ assoᵣ assoᵣ i = ?
    --thm₁ eq eq i = refl
    --thm₁ (r ∙ r₁) (x ∙ x₁) i = thm₁ ? ? (i ⟨ r ⟩) ⊡ ?
    ----lem₁ r₁ ? x (i ⟨ r ⟩) ⊡ ?
    --thm₁ (r ⊕ r₁) (x ⊕ x₁) i = ?
    --thm₁ (up r) (up x) i = ?
    --thm₁ (down r) (down x) i = ?
    --thm₁ swap () i
    --thm₁ assoₗ assoₗ i = ?
    --thm₁ assoᵣ assoᵣ i = ?

