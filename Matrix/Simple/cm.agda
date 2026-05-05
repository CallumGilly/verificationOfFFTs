
module Matrix.Simple.cm where
  open import Data.Nat
  open import Data.Nat.Properties
  open import Relation.Binary.PropositionalEquality

  open import Matrix.Simple.Base
  open import Matrix.Simple.Reshape

  S = Shape
  P = Position
  transp = recursive-transpose
  infix 4 _⊡_
  _⊡_ = trans
  
  variable
    s p : S
    n m k : ℕ


  cm₂ : Reshape (s ⊗ p) (p ⊗ s)
  cm₂ {s} = ♯ ∙ reindex (*-comm (length s) _) ∙ ♭

  cm : Reshape s (transp s)
  cm {ι n} = eq
  cm {s ⊗ p} = cm ⊕ cm ∙ cm₂

  s-sᵗ : ∀ s → length s ≡ length (transp s) 
  s-sᵗ (ι n) = refl
  s-sᵗ (s ⊗ p) = *-comm (length s) (length p) 
                 ⊡ cong₂ _*_ (s-sᵗ p) (s-sᵗ s)


  xs-sᵗ : ∀ s → length s ≡ length (transp s) 
  xs-sᵗ (ι n) = refl
  xs-sᵗ (s ⊗ p) = cong₂ _*_ (xs-sᵗ s) (xs-sᵗ p) 
                  ⊡ *-comm (length (transp s)) _

  cm-orig : Reshape s (transp s)
  cm-orig {s} = ♯ ∙ reindex (s-sᵗ s) ∙ ♭

  lemma : (i : P (ι n)) → (p : k ≡ m) (q : m ≡ n) → i ⟨ reindex (p ⊡ q) ⟩ ≡ i ⟨ reindex q ⟩ ⟨ reindex p  ⟩ 
  lemma i refl refl = refl

  lemma-cong-* : ∀ {m' n'} → (i : P (ι m)) (j : P (ι n)) (p : m' ≡ m) (q : n' ≡ n) 
               → (i ⊗ j) ⟨ split ⟩ ⟨ reindex (cong₂ _*_ p q) ⟩
                 ≡ ((i ⟨ reindex p ⟩) ⊗ (j ⟨ reindex q ⟩)) ⟨ split ⟩
  lemma-cong-* i j refl refl = refl

  cm-step-thm : (i : P (transp s)) → i ⟨ cm ⟩ ≡ i ⟨ cm-orig ⟩
  cm-step-thm {ι n}   i       = refl
  cm-step-thm {s ⊗ p} (i ⊗ j) 
    rewrite 
        cm-step-thm i
      | cm-step-thm j 
      | rev-eq {s = p} ♭ ((i ⟨ rev ♭ ⟩) ⟨ reindex (s-sᵗ p) ⟩)
      | rev-eq {s = s} ♭ ((j ⟨ rev ♭ ⟩) ⟨ reindex (s-sᵗ s) ⟩)
      | lemma (((i ⟨ rev ♭ ⟩) ⊗ (j ⟨ rev ♭ ⟩)) ⟨ split ⟩) (*-comm (length s) (length p))
              (cong₂ _*_ (s-sᵗ p) (s-sᵗ s))
      | lemma-cong-* (i ⟨ rev ♭ ⟩) (j ⟨ rev ♭ ⟩) (s-sᵗ p) (s-sᵗ s)
      = refl


  ⊕-compose : ∀ {s p q r w u} 
            → (a : Reshape p w) (b : Reshape r u)
            → (c : Reshape s p) (d : Reshape q r)
            → ∀ i → i ⟨ a ⊕ b ⟩ ⟨ c ⊕ d ⟩ ≡ i ⟨ (a ∙ c) ⊕ (b ∙ d) ⟩
  ⊕-compose a b c d (i ⊗ j) = refl


  ⊕-rev-eq : ∀ {s p q r}
           → (a : Reshape s p) (b : Reshape q r)
           → ∀ i → i ⟨ (a ∙ rev a) ⊕ (b ∙ rev b) ⟩ ≡ i
  ⊕-rev-eq a b (i ⊗ j) = cong₂ _⊗_ (rev-eq a i) (rev-eq b j)

  flat-cm : ∀ {s} 
          → (i : P (transp s))
          → i ⟨ cm ∙ ♯ ⟩ ≡ i ⟨ ♯ ∙ reindex (s-sᵗ s) ⟩ 
  flat-cm {ι n} i = refl
  flat-cm {s ⊗ p} (i ⊗ j) 
    rewrite 
        cm-step-thm (i ⊗ j)
      | ⊕-compose {p = ( s)}{r = (p)} 
        ♭ ♭ ♯ ♯  
        ((i ⊗ j) ⟨ ♯ ∙ reindex (s-sᵗ (s ⊗ p))  ∙ flat ⟩)
      | ⊕-rev-eq {s = s}{q = p}  
        ♭ ♭
        ((i ⊗ j) ⟨ ♯ ∙ reindex (s-sᵗ (s ⊗ p))  ∙ flat ⟩)
      | rev-eq 
        (flat {length s})
        ((i ⊗ j) ⟨ ♯ ∙ reindex (s-sᵗ (s ⊗ p))   ⟩)
    = refl


  reindex-prop₁ : ∀ {s p q r}
               → (a : s ≡ p) (b : q ≡ r)
               → ∀ i j
               → ((i ⟨ reindex a ⟩) ⊗ (j ⟨ reindex b ⟩)) ⟨ ♯ ∙ reindex (*-comm q s) ⟩
                 ≡ (i ⊗ j) ⟨ ♯ ∙ reindex (*-comm q s ⊡ cong₂ _*_ a b ) ⟩
  reindex-prop₁ {s} {q = q} refl refl i j with ((i ⊗ j) ⟨ split ⟩)
  ... | (ι ij) 
        rewrite 
            reindex-cast (*-comm q s) ij
          | reindex-cast (*-comm q s ⊡ refl) ij
          = refl

  reindex-prop₂ : ∀ {m n k l}
                → (i : P (ι (m * n)))
                → (a : k ≡ n) (b : l ≡ m)
                → i ⟨ reindex (*-comm n m) ∙ flat ∙ (reindex a ⊕ reindex b) ⟩
                  ≡ i ⟨ reindex (cong₂ _*_ a b ⊡ *-comm n m) ∙ flat ⟩
  reindex-prop₂ {m} {n = n} i refl refl with i ⟨ reindex (*-comm n m) ∙ flat {n} ⟩
  ... | (i′ ⊗ j′)= refl

  dbl-reshape : ∀ {s p q r}
              → (a b : Reshape s p) (c d : Reshape q r)
              → (pa : ∀ i → i ⟨ a ⟩ ≡ i ⟨ b ⟩)
              → (pb : ∀ i → i ⟨ c ⟩ ≡ i ⟨ d ⟩)
              → ∀ i → i ⟨ a ⊕ c ⟩ ≡ i ⟨ b ⊕ d ⟩
  dbl-reshape a b c d pa pb (i ⊗ j) = cong₂ _⊗_ (pa i) (pb j)


  rev-eq₃ : ∀ {s p q r}
         → (a : Reshape s p) (b : Reshape q p) (c : Reshape r q)
         → ∀ i → i ⟨ a ∙ rev a ∙ b ∙ c ⟩ ≡ i ⟨ b ∙ c ⟩
  rev-eq₃ a b c i = cong (λ x → x ⟨ b ∙ c ⟩) (rev-eq a i)

  thm : ∀ {s p} → (i : P (transp s)) (j : P (transp p))
      → (i ⊗ j) ⟨ cm₂ ∙ (cm ⊕ cm) ⟩ ≡ ((i ⊗ j) ⟨ cm ⟩)
  thm {s} {p} i j 
    rewrite
        flat-cm i
      | flat-cm j
      | reindex-prop₁ (s-sᵗ s) (s-sᵗ p) (i ⟨ ♯ ⟩) (j ⟨ ♯ ⟩)
      | dbl-reshape cm cm-orig cm cm-orig (cm-step-thm) (cm-step-thm) ((i ⊗ j) ⟨ cm₂ ⟩)
      | ⊕-compose {s = p}{q = s} 
        ♭ ♭ cm-orig cm-orig 
        ((i ⊗ j) ⟨ ♯ ∙ reindex (*-comm (length (transp p)) _)  ∙ flat ⟩)
      | dbl-reshape {s = p}{q = s} 
           ((♭ {transp p}) ∙ rev ♭ ∙ (reindex (s-sᵗ p)) ∙ ♭) 
           ((reindex (s-sᵗ p)) ∙ ♭)
           ((♭ {transp s}) ∙ rev ♭ ∙ (reindex (s-sᵗ s)) ∙ ♭) 
           ((reindex (s-sᵗ s)) ∙ ♭)
        (rev-eq₃ (♭ {transp p}) (reindex (s-sᵗ p)) ♭)
        (rev-eq₃ (♭ {transp s}) (reindex (s-sᵗ s)) ♭)
        ((i ⊗ j) ⟨  ♯ ∙ reindex (*-comm (length (transp p)) _)  ∙ flat ⟩)
      | sym ((⊕-compose {s = p}{q = s} 
               (reindex (s-sᵗ p)) (reindex (s-sᵗ s)) ♭ ♭ 
               ((i ⊗ j) ⟨  ♯ ∙ reindex (*-comm (length (transp p)) _)  ∙ flat ⟩)))
      | reindex-prop₂ 
          ((i ⊗ j) ⟨  ♯ ⟩)
          (s-sᵗ p) (s-sᵗ s)
    with ((i ⊗ j) ⟨  ♯ ⟩)

  ... | (ι ij) 
        rewrite
            reindex-cast (cong₂ _*_ (s-sᵗ p) (s-sᵗ s) ⊡ *-comm (length (transp p)) _) ij
          | reindex-cast (*-comm (length p) (length s) ⊡ cong₂ _*_ (s-sᵗ s) (s-sᵗ p) ) ij
        = refl



