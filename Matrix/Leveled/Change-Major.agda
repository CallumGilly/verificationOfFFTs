{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --without-K #-}

open import Matrix.Mon

module Matrix.Leveled.Change-Major (M : Mon) where
open Mon M
open import Matrix.Leveled.Base M
open import Matrix.Leveled.Reshape M
open import Data.Product
open import Function

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning

private
  variable 
    l : L
    X : Set
  
record Change-Major : Set₁ where
  field
    BaseCM : ∀ {s p : S (ss zz)} → Reshape (ν (u-flatten-z (flatten-z s) ● u-flatten-z (flatten-z p))) (ν (u-flatten-z (flatten-z p) ● u-flatten-z (flatten-z s)))
    
  CM : ∀ {s p : S (ss l)} → Reshape (s ⊗ p) (p ⊗ s)
  CM {zz  } {s} {p} = (rev flatten-zᵣ) 
                    ∙ BaseCM {s} {p}
                    ∙ flatten-zᵣ
  CM {ss l} {s} {p} = (rev flatten-zᵣ) 
                    ∙ CM {l}
                    ∙ flatten-zᵣ


  CMᵗ : ∀ {s : S l} → Reshape (transp s) s
  CMᵗ {.zz} {ν x} = eq
  CMᵗ {.(ss _)} {ι s} = eq
  CMᵗ {.(ss _)} {s ⊗ s₁} = CMᵗ ⊕ CMᵗ ∙ CM
  
  module CMᵗ-prfs where
      
    private
      infix 4 _⊡_
      _⊡_ = trans

    
    -- As well as defining CM with flatten-zᵣ - we should also be able to define
    -- CM with u-flatten and prove they are equivalent
    CM′ : ∀ {s p : S (ss l)} → Reshape (s ⊗ p) (p ⊗ s)
    CM′ {l} {s} {p} = (rev ν-flattenᵣ) 
                    ∙ BaseCM {ι (ν (u-flatten s))} {ι (ν (u-flatten p))}
                    ∙ ν-flattenᵣ

    {-
    lemma₂ : ∀ {s : S (ss (ss l))} 
           → ∀ {i : P s} 
           → i ⟨ rev flatten-zᵣ ⟩ ⟨ rev ν-flattenᵣ ⟩ 
             ≡ 
             ? --i ⟨ rev ν-flattenᵣ ⟩
    -}

    CM-CM′ : ∀ {s p : S (ss l)} (i : P (s ⊗ p)) → i ⟨ CM ⟩ ≡ i ⟨ CM′ ⟩
    CM-CM′ {zz} {s} {p} (i ⊗ j) = ?
    CM-CM′ {ss l} {s} {p} (i ⊗ j) rewrite CM-CM′ ((i ⟨ rev flatten-zᵣ ⟩) ⊗ (j ⟨ rev flatten-zᵣ ⟩)) = ?

    -------------------------------------------------------------------
    --- To prove CMᵗ-lemma, the first important observation is that ---
    --- there are two ways to structure the following proof.        ---
    -------------------------------------------------------------------

    -- Applying commutativity first
    s-sᵗ : ∀ (s : S l) → length s ≡ length (transp s)
    s-sᵗ (ν _) = refl
    s-sᵗ (ι _) = refl
    s-sᵗ (s ⊗ p) = comm
                  ⊡ cong₂ _●_ (s-sᵗ p) (s-sᵗ s)
    --- And applying the recursive step first.
    xs-sᵗ : ∀ (s : S l) → length s ≡ length (transp s)
    xs-sᵗ (ν _) = refl
    xs-sᵗ (ι _) = refl
    xs-sᵗ (s ⊗ p) = cong₂ _●_ (xs-sᵗ s) (xs-sᵗ p)
                  ⊡ comm

    -- I don't think we can use this version of flattening, as we can't 
    -- reduce down to ● easily...
    asdf♭s-sᵗ : ∀ (s : S (ss l)) → flatten-z (transp s) ≡ flatten-z s
    asdf♭s-sᵗ (ι s) = refl
    asdf♭s-sᵗ (s ⊗ s₁) = ?


    -- But we can do it if we go all the way to ν
    ♭s-sᵗ : ∀ (s : S (ss l)) → u-flatten (transp s) ≡ u-flatten s
    ♭s-sᵗ {l} (ι s) = refl
    ♭s-sᵗ {l} (s ⊗ p) = comm 
                       ⊡ cong₂ _●_ (♭s-sᵗ s) (♭s-sᵗ p)

    x♭s-sᵗ : ∀ (s : S (ss l)) → u-flatten (transp s) ≡ u-flatten s
    x♭s-sᵗ {l} (ι s) = refl
    x♭s-sᵗ {l} (s ⊗ p) = cong₂ _●_ (x♭s-sᵗ p) (x♭s-sᵗ s)
                       ⊡ comm



    --- This is the difference between our two possible definitions of CMᵗ
    
    private
      -- We then need to reinvent reindex and equate CM to reindex
      -- I have placed this in a private block, as I want to avoid using
      -- reindex wherever possible outside of this proof.
      reindex : ∀ {m n : U} → (m ≡ n) → Reshape (ι (ν m)) (ι (ν n))
      reindex {m} prf = subst (λ t → Reshape (ι (ν m)) (ι (ν t))) prf eq

      reindex′ : {s₁ : S l} {s₂ : S l} → (s₁ ≡ s₂) → Reshape s₁ s₂
      reindex′ {_} {s₁} {s₂} prf = subst (λ t → Reshape s₁ t) prf eq

    -- Not true as r := CMᵗ ∙ transpᵣ : Reshape s s, and yet reorders the elements preventing this from holding
    -- eq-lemma : ∀ {l : L} → ∀ {s : S l} → ∀ (r : Reshape s s) → ∀ i → i ⟨ r ⟩ ≡ i

    helper : ∀ {lₛ lₚ lₖ : L} {s : S lₛ} {p : S lₚ} {k : S lₖ}
           → (r₁ r₂ : Reshape s p) 
           → (r     : Reshape k s)
           → (∀ i → i ⟨ r₁ ∙ r ⟩ ≡ i ⟨ r₂ ∙ r ⟩)
           → ∀ i → i ⟨ r₁ ⟩ ≡ i ⟨ r₂ ⟩
    helper {lₛ} {lₚ} {s} {p} r₁ r₂ r prf i = ?

    rshpEq : ∀ {lₛ lₚ : L} {s₁ s₂ : S lₛ} {p₁ p₂ : S lₚ}
           → (r₁ : Reshape s₁ p₁)
           → (r₂ : Reshape s₂ p₂)
           → (s₁≡s₂ : s₁ ≡ s₂)
           → (p₁≡p₂ : p₁ ≡ p₂)
           → (∀ i → i ⟨ r₁ ∙ rev ν-flattenᵣ ⟩ ≡ i ⟨ reindex′ (sym p₁≡p₂) ∙ r₂ ∙ rev ν-flattenᵣ ∙ reindex′ (cong ν (cong u-flatten s₁≡s₂)) ⟩)
           → (∀ i → i ⟨ r₁ ⟩ ≡ i ⟨ reindex′ (sym p₁≡p₂) ∙ r₂ ∙ reindex′ s₁≡s₂ ⟩)
    rshpEq {lₛ} {lₚ} {s₁} {.s₁} {p₁} {.p₁} r₁ r₂ refl refl prf i = 
      let tmo = prf i
      in helper r₁ r₂ (rev ν-flattenᵣ) prf i

    semi-flatten : S (ss l) → S (ss l)
    semi-flatten = ι ∘ flatten-z 

    semi-flattenᵣ : ∀ {s : S (ss l)} → Reshape s (semi-flatten s)
    semi-flattenᵣ {l} {s} = up flatten-zᵣ

    CMᵗ-reindex : ∀ {s : S (ss l)} → Reshape (transp s) s
    CMᵗ-reindex {l} {s} = rev (u-flattenᵣ) ∙ reindex (♭s-sᵗ s) ∙ (u-flattenᵣ)


    lemma : ∀ {n m k : U} 
          → ∀ (i : P (ι (ν n))) 
          → (p : k ≡ m) (q : m ≡ n) 
          → i ⟨ reindex (p ⊡ q) ⟩ ≡ i ⟨ reindex q ⟩ ⟨ reindex p ⟩
    lemma i refl refl = refl

    {-
    lemma-cong-● : ∀ {m n m′ n′ : U} 
                 → (i : P (ι (ν m)))
                 → (j : P (ι (ν n)))
                 → (p : m′ ≡ m)
                 → (q : n′ ≡ n)
                 → ? --(i ⊗ j) ⟨ split ⟩ ⟨ reindex ? ⟩ ≡ ?
    -}
    
    --flat-CMᵗ : ∀ {s : S (ss l)}
    --         → (i : P (transp s))
    --         → i ⟨ CMᵗ ∙ flatten-zᵣ ⟩ ≡ i ⟨ flatten-zᵣ ∙ (reindex ?) ⟩

    --CM-lemma₁ : ∀ {s : S (ss (ss l))} (i : P (transp s)) → i ⟨ CMᵗ ⟩ ⟨ rev flatten-zᵣ ⟩ ≡ i ⟨ rev flatten-zᵣ ⟩ ⟨ CMᵗ ⟩ ⟨ ? ⟩
    CM-lemma₂ : ∀ {s p : S (ss (ss l))} 
              → (i : P s) (j : P p) 
              → ((i ⟨ rev flatten-zᵣ ⟩) ⊗ (j ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩ ≡ (i ⊗ j) ⟨ CM ⟩ ⟨ rev flatten-zᵣ ⟩
    CM-lemma₂ {l} {s} {p} i j = sym (⊕-rev-eq-lemma _ _ _)
                              ⊡ sym (⊕-distributes-∙ _ _ _ _ (((i ⟨ rev flatten-zᵣ ⟩) ⊗ (j ⟨ rev flatten-zᵣ ⟩)) ⟨ CM ⟩))
    --CM-lemma₃ : ∀ {s : S (ss (ss l))} (i : P (s)) → i ⟨ CMᵗ ⟩ ⟨ flatten-zᵣ {_} {?} ⟩ ≡ i ⟨ flatten-zᵣ ⟩ ⟨ CMᵗ ⟩ ⟨ ? ⟩

    CMᵗ-lemma : ∀ {s p : S (ss l)} 
              → ∀ (i : P (transp (s ⊗ p)))
              → i ⟨ CM ∙ (CMᵗ ⊕ CMᵗ) ⟩ ≡ i ⟨ (CMᵗ ⊕ CMᵗ) ∙ CM ⟩
    CMᵗ-lemma {zz} {s} {p} (i ⊗ j) = ?
    CMᵗ-lemma {ss l} {s} {p} (i ⊗ j) = ?
    --CMᵗ-lemma {zz} {s} {p} (i ⊗ j) = ?
    --CMᵗ-lemma {ss l} {s} {p} (i ⊗ j)  = ?
    
  open CMᵗ-prfs public




















