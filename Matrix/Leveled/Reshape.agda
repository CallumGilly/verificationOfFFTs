open import Matrix.Mon

module Matrix.Leveled.Reshape (M : Mon) where
  open Mon M
  open import Matrix.Leveled.Base M

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
      l r w : L
      u : U
      X : Set

  infixl 5 _∙_
  data Reshape : {l r : L} → S l → S r → Set where
    eq     : ∀ {s : S l} → Reshape s s 
    _∙_    : ∀ {s : S l}{p : S r}{q : S w} → Reshape p q → Reshape s p → Reshape s q
    _⊕_    : ∀ {s p : S (ss l)}{q t : S (ss r)} → Reshape s q → Reshape p t → Reshape (s ⊗ p) (q ⊗ t)
    up     : ∀ {s : S l}{p : S r} → Reshape s p → Reshape s (ι p)
    down   : ∀ {s : S l}{p : S r} → Reshape s p → Reshape (ι s) p
    flat   : ∀ {m n} → Reshape (ι (ν m) ⊗ ι (ν n)) (ν (m ● n))
    unflat : ∀ {m n} → Reshape (ν (m ● n)) (ι (ν m) ⊗ ι (ν n))
    swap   : ∀ {s p : S (ss l)} → Reshape (s ⊗ p) (p ⊗ s)
    
  _⟨_⟩ : {s : S l} {p : S r} → P s → Reshape p s → P p
  i ⟨ eq ⟩ = i
  i ⟨ r₁ ∙ r₂ ⟩ = i ⟨ r₁ ⟩ ⟨ r₂ ⟩
  (i₁ ⊗ i₂) ⟨ r₁ ⊕ r₂ ⟩ = (i₁ ⟨ r₁ ⟩) ⊗ (i₂ ⟨ r₂ ⟩)
  ι i ⟨ up r ⟩ = i ⟨ r ⟩
  i ⟨ down r ⟩ = ι (i ⟨ r ⟩)
  ν x ⟨ flat ⟩ = let em , en = (Inverse.to $ pair-law _ _) x in (ι (ν em) ⊗ ι (ν en))
  (ι (ν x₁) ⊗ ι (ν x₂)) ⟨ unflat ⟩ = ν ((Inverse.from $ pair-law _ _) (x₁ , x₂)) 
  (i₁ ⊗ i₂) ⟨ swap ⟩ = i₂ ⊗ i₁

  reshape : {s : S l}{p : S r} → Reshape s p → Ar s X → Ar p X
  reshape r a i = a (i ⟨ r ⟩)

  rev : ∀ {s : S l} {p : S r} → Reshape s p → Reshape p s
  rev eq = eq
  rev (r₁ ∙ r₂) = rev r₂ ∙ rev r₁
  rev (r₁ ⊕ r₂) = rev r₁ ⊕ rev r₂
  rev (up r) = down (rev r)
  rev (down r) = up (rev r)
  rev flat = unflat
  rev unflat = flat
  rev swap = swap

  rev-eq′ : ∀ {s : S l} {p : S r}
         → ∀ (r : Reshape s p)
         → ∀ (i : P s)
         → i ⟨ rev r ∙ r ⟩ ≡ i  
  rev-eq′ eq i = refl
  rev-eq′ (r₁ ∙ r₂) i rewrite rev-eq′ r₁ (i ⟨ rev r₂ ⟩) = rev-eq′ r₂ i
  rev-eq′ (r₁ ⊕ r₂) (i₁ ⊗ i₂) = cong₂ _⊗_ (rev-eq′ r₁ i₁) (rev-eq′ r₂ i₂)
  rev-eq′ (up r) i = rev-eq′ r i
  rev-eq′ (down r) (ι i) = cong ι (rev-eq′ r i)
  rev-eq′ flat (ι (ν x₁) ⊗ ι (ν x₂)) = let 
      inv = (Inverse.inverse (pair-law _ _) .proj₁) refl 
    in cong₂ _⊗_ (cong ι (cong ν (,-injectiveˡ inv))) (cong ι (cong ν (,-injectiveʳ inv)))
  rev-eq′ unflat (ν x) = cong ν (Inverse.inverse (pair-law _ _) .proj₂ refl)
  rev-eq′ swap (i₁ ⊗ i₂) = refl

  rev-rev : ∀ {s : S l} {p : S r}
         → ∀ (r : Reshape s p)
         → ∀ (i : P p)
         → i ⟨ rev (rev r) ⟩ ≡ i ⟨ r ⟩  
  rev-rev eq i = refl
  rev-rev (r₁ ∙ r₂) i rewrite rev-rev r₂ (i ⟨ rev (rev r₁) ⟩) | rev-rev r₁ i = refl
  rev-rev (r₁ ⊕ r₂) (i₁ ⊗ i₂) = cong₂ _⊗_ (rev-rev r₁ i₁) (rev-rev r₂ i₂)
  rev-rev (up r) (ι i) = rev-rev r i
  rev-rev (down r) i = cong ι (rev-rev r i)
  rev-rev flat i = refl
  rev-rev unflat i = refl
  rev-rev swap i = refl
  
  rev-eq : ∀ {s : S l} {p : S r}
         → ∀ (r : Reshape s p)
         → ∀ (i : P p)
         → i ⟨ r ∙ rev r ⟩ ≡ i  
  rev-eq r i rewrite sym (rev-rev r i) = rev-eq′ (rev r) i

  tmp : ∀ {l o : L} {s : S l} {p : S o} 
      → ∀ (xs ys : Ar s X) 
      → ∀ (r : Reshape {l} {o} s p)
      → ∀ (prf : ∀ (i : P s) → xs i ≡ ys i)
      → ∀ (i : P p) → xs (i ⟨ r ⟩) ≡ ys (i ⟨ r ⟩)
  tmp xs ys r prf i = prf (i ⟨ r ⟩)
  --tmp xs ys eq prf i = prf i
  --tmp xs ys (_∙_ r₁ r₂) prf i = tmp xs ys r₂ prf (i ⟨ r₁ ⟩) 
  --tmp xs ys (r₁ ⊕ r₂) prf (i₁ ⊗ i₂) = prf ((i₁ ⟨ r₁ ⟩) ⊗ (i₂ ⟨ r₂ ⟩))
  --tmp xs ys (up r) prf i = prf (i ⟨ up r ⟩)
  --tmp xs ys (down r) prf i = ?
  --tmp xs ys swap prf i = ?

  transp : S l → S l
  transp (ν x) = ν x
  transp (ι s) = ι s
  transp (s ⊗ p) = transp p ⊗ transp s
  
  transpᵣ : ∀ {s : S l} → Reshape (transp s) s
  transpᵣ {_} {ν x} = eq
  transpᵣ {_} {ι s} = eq
  transpᵣ {_} {s₁ ⊗ s₂} = (transpᵣ ⊕ transpᵣ) ∙ swap

  flatten : S (ss (ss l)) → S (ss l)
  flatten (ι s) = s
  flatten (s ⊗ p) = flatten s ⊗ flatten p
  
  flattenᵣ : ∀ {s : S (ss (ss l))} → Reshape s (flatten s)
  flattenᵣ {l} {ι s} = down eq
  flattenᵣ {l} {s ⊗ s₁} = flattenᵣ ⊕ flattenᵣ

  u-flatten : S l → U
  u-flatten (ν x) = x
  u-flatten (ι s) = u-flatten s
  u-flatten (s ⊗ p) = u-flatten s ● u-flatten p
  
  u-flattenᵣ : ∀ {s : S (ss l)} → Reshape s (ι (ν (u-flatten s)))
  u-flattenᵣ {_} {s ⊗ s₁} = up flat ∙ (u-flattenᵣ ⊕ u-flattenᵣ)
  u-flattenᵣ {zz} {ι (ν x)} = eq
  u-flattenᵣ {ss l} {ι s} = down u-flattenᵣ

  ν-flattenᵣ : ∀ {s : S l} → Reshape s (ν (u-flatten s))
  ν-flattenᵣ {.(ss _)} {s ⊗ s₁} = flat ∙ (up ν-flattenᵣ ⊕ up ν-flattenᵣ)
  ν-flattenᵣ {.zz} {ν x} = eq
  ν-flattenᵣ {.(ss _)} {ι s} = down ν-flattenᵣ

  u-flatten-z : S zz → U
  u-flatten-z (ν x) = x

  u-flatten-z-id : ∀ {s : S zz} → Reshape s (ν (u-flatten-z s))
  u-flatten-z-id {ν x} = eq

  flatten-z : S (ss l) → S l
  flatten-z {l} (ι x) = x
  flatten-z {zz} (x ⊗ y) = ν (u-flatten-z (flatten-z x) ● u-flatten-z (flatten-z y))
  flatten-z {ss l} (x ⊗ y) = (flatten-z x) ⊗ (flatten-z y)

  flatten-zᵣ : ∀ {s : S (ss l)} → Reshape s (flatten-z s)
  flatten-zᵣ {l} {ι s} = down eq
  flatten-zᵣ {zz} {s ⊗ s₁} = flat ∙ ((up u-flatten-z-id ∙ flatten-zᵣ) ⊕ (up u-flatten-z-id ∙ flatten-zᵣ))
  flatten-zᵣ {ss l} {s ⊗ s₁} = flatten-zᵣ ⊕ flatten-zᵣ

  ⊗-remQuot : ∀ {s : S (ss l)} (p : S (ss l)) → P (s ⊗ p) → P s × P p
  ⊗-combine : ∀ {s p : S (ss l)} → P s → P p → P (s ⊗ p)
  
  ⊗-remQuot-combine : ∀ {s p : S (ss l)}
                     → ∀ (i : P s)
                     → ∀ (j : P p)
                     → ⊗-remQuot p (⊗-combine i j) ≡ (i , j)

  ⊗-combine-remQuot : ∀ {s : S (ss l)}
                     → ∀ (p : S (ss l))
                     → ∀ (i : P (s ⊗ p))
                     → uncurry ⊗-combine (⊗-remQuot p i) ≡ i

  ⊗-remQuot _ (i₁ ⊗ i₂) = i₁ , i₂
  ⊗-combine i₁ i₂ = i₁ ⊗ i₂
  ⊗-remQuot-combine i₁ i₂ = refl
  ⊗-combine-remQuot _ (i₁ ⊗ i₂) = refl

  remQuot-splits-proof : ∀ {X : Set}
                      → ∀ {s p : S (ss l)}
                      → ∀ {xs ys : Ar (s ⊗ p) X}
                      → ∀ (prf : ∀ (i : P s) (j : P p) → xs (i ⊗ j) ≡ ys (i ⊗ j))
                      → ∀ (i : P (s ⊗ p)) → xs i ≡ ys i
  remQuot-splits-proof prf (i₁ ⊗ i₂) = prf i₁ i₂

  proj₁-remQuot-⊕ : ∀ {l₁ : L} {s₁ s₂ : S (ss l₁)}
                  → ∀ {l₂ : L} {p₁ p₂ : S (ss l₂)}
                  → ∀ (i : P (s₁ ⊗ s₂))
                  → ∀ (r₁ : Reshape p₁ s₁)
                  → ∀ (r₂ : Reshape p₂ s₂)
                  → proj₁ (⊗-remQuot p₂ (i ⟨ r₁ ⊕ r₂ ⟩)) ≡ (proj₁ (⊗-remQuot s₂ i)) ⟨ r₁ ⟩ 
  proj₁-remQuot-⊕ (i₁ ⊗ i₂) r₁ r₂ = refl

  proj₂-remQuot-⊕ : ∀ {l₁ : L} {s₁ s₂ : S (ss l₁)}
                  → ∀ {l₂ : L} {p₁ p₂ : S (ss l₂)}
                  → ∀ (i : P (s₁ ⊗ s₂))
                  → ∀ (r₁ : Reshape p₁ s₁)
                  → ∀ (r₂ : Reshape p₂ s₂)
                  → proj₂ (⊗-remQuot p₂ (i ⟨ r₁ ⊕ r₂ ⟩)) ≡ (proj₂ (⊗-remQuot s₂ i)) ⟨ r₂ ⟩ 
  proj₂-remQuot-⊕ (i₁ ⊗ i₂) _ _ = refl

  proj₁-remQuot-cong : ∀ {s p : S (ss l)}
                     → ∀ {i j : P (s ⊗ p)} 
                     → (prf : i ≡ j)
                     → proj₁ (⊗-remQuot p i) ≡ proj₁ (⊗-remQuot p j)
  proj₁-remQuot-cong refl = refl

  proj₂-remQuot-cong : ∀ {s p : S (ss l)}
                     → ∀ {i j : P (s ⊗ p)} 
                     → (prf : i ≡ j)
                     → proj₂ (⊗-remQuot p i) ≡ proj₂ (⊗-remQuot p j)
  proj₂-remQuot-cong refl = refl





















  --u₂ : ∀ {s : S (ss l)} → Reshape s (ν (u-flatten s))
  --u₂ {_} {s ⊗ s₁} = ?
  --u₂ {zz} {ι (ν x)} = down eq
  --u₂ {ss l} {ι s} = down u₂

  {-
  u-flattenᵣ : ∀ {s : S l} → Reshape s (ν (u-flatten s))
  u-flattenᵣ {_} {ν _} = eq
  u-flattenᵣ {_} {ι _} = down u-flattenᵣ
  u-flattenᵣ {_} {_ ⊗ _} = flat ∙ (? ⊕ ?) --flat ∙ (u-flattenᵣ ⊕ u-flattenᵣ)
  -}
  
  {-
  open import Matrix.Parameterised.Base M
  open import Matrix.Parameterised.Reshape M
  open Mon M

  lower-S : S → U
  lower-S = size

  lower-P : ∀ {s : S} → P s → El (lower-S s)
  lower-P (ι x) = x
  lower-P (i₁ ⊗ i₂) = (Inverse.from $ pair-law _ _) (lower-P i₁ , lower-P i₂)

  raise-P : ∀ {s : S} → El (lower-S s) → P s 
  raise-P {ι x} i = ι i
  raise-P {s ⊗ s₁} i = let x₁ , x₂ = (Inverse.to $ pair-law _ _) i in raise-P x₁ ⊗ raise-P x₂ 

  inv₁ : ∀ {s : S} → (i : P s) → raise-P (lower-P i) ≡ i
  inv₁ {ι _} (ι _) = refl
  inv₁ {s₁ ⊗ s₂} (i₁ ⊗ i₂) = let
      inverse₁ = 
        Inverse.inverse 
          (pair-law (lower-S s₁) (lower-S s₂)) 
          .proj₁ 
          {lower-P i₁ , lower-P i₂} 
          {lower-P {s₁ ⊗ s₂} (i₁ ⊗ i₂)} 
          refl 
      left  = ,-injectiveˡ inverse₁
      right = ,-injectiveʳ inverse₁
      in 
      (cong₂ _⊗_) (cong raise-P left ⊡ inv₁ i₁) (cong raise-P right ⊡ inv₁ i₂)

  inv₂ : ∀ {s : S} → (i : El (lower-S s)) → lower-P {s} (raise-P i) ≡ i
  inv₂ {ι x} i = refl
  inv₂ {s₁ ⊗ s₂} i = 
      let
        i₁ , i₂ = Inverse.to (pair-law (lower-S s₁) (lower-S s₂)) i
        inverse₂ = 
          Inverse.inverse 
            (pair-law (lower-S s₁) (lower-S s₂)) 
            .proj₂ 
            {i}
            {i₁ , i₂} 
            refl
      in 
          cong 
            (Inverse.from (pair-law (lower-S s₁) (lower-S s₂))) 
            (cong₂ _,_ (inv₂ {s₁} i₁) (inv₂ {s₂} i₂)) 
        ⊡ inverse₂
  
  lower-Ar : ∀ {s : S} → ∀ {X : Set} → Ar s X → El (lower-S s) → X
  lower-Ar xs = xs ∘ raise-P 

  raise-Ar : ∀ {s : S} → ∀ {X : Set} → (El (lower-S s) → X) → Ar s X
  raise-Ar xs = xs ∘ lower-P
  -}
