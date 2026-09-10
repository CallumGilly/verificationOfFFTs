Here I define the translation from the DSL back to standard Agda I can then 
equate to my Agda implementation
```agda


open import ComplexNew
open import Matrix.NatMon
open import Matrix.Leveled.NatMon-Change-Major 
--(spec : FFT-Specification cplx ℕ-Mon ℕ-CM)
module CodeGeneration.Translate-Agda (cplx : Cplx)  where
open import Function

open import Data.Nat renaming (_*_ to _*ₙ_)

open Cplx cplx

open import FFT.Leveled.dft cplx
open import FFT.Leveled.Specification cplx ℕ-Mon ℕ-CM
open FFT-Specification ℕ-dft
open import FFT.Leveled.UFFT cplx ℕ-Mon --ℕ-CM ℕ-dft
open import FFT.Leveled.Properties cplx ℕ-Mon ℕ-CM ℕ-dft

open import Matrix.Leveled.Base ℕ-Mon
open import Matrix.Leveled.Reshape ℕ-Mon
open import Matrix.Leveled.SubShape ℕ-Mon
open import Matrix.Leveled.Change-Major ℕ-Mon
open Change-Major ℕ-CM

open import CodeGeneration.DSL
open import Relation.Binary.PropositionalEquality

import Algebra.Structures as AlgebraStructures
import Algebra.Definitions as AlgebraDefinitions
open AlgebraStructures  {A = ℂ} _≡_
open AlgebraDefinitions {A = ℂ} _≡_

open IsCommutativeRing +-*-isCommutativeRing hiding (trans; refl; sym)
```

We first need a translation between DSL types, and our Agda types.
This actually becomes the "Context" we are working within
```agda
translate-Ty : Ty → Set
translate-Ty C = ℂ
translate-Ty N = ℕ
translate-Ty (ix i) = P i
translate-Ty (x ⇒ y) = (translate-Ty x) → (translate-Ty y)
```

Given this we then need to create two translators - that for the set of in place 
operations and that for the set of arithmetic operations. 
```agda
translate-Arit : {τ : Ty} → Arit translate-Ty τ → translate-Ty τ
translate-Inp : ∀ {ℓ : L} {s : S ℓ} → Inp translate-Ty s → translate-Ty (ix s ⇒ C) → translate-Ty (ix s ⇒ C)
```

```agda
Pₗ : ∀ {l : L} {s p : S (ss l)} → P (s ⊗ p) → P s
Pₗ (i ⊗ _) = i

Pᵣ : ∀ {l : L} {s p : S (ss l)} → P (s ⊗ p) → P p
Pᵣ (_ ⊗ i) = i

translate-Arit (var x) = x
translate-Arit (lam x) = λ y → translate-Arit (x y)
translate-Arit (app arit₁ arit₂) = (translate-Arit arit₁) (translate-Arit arit₂)
translate-Arit (sizeN {s = s} arit) = length s
translate-Arit (posiN arit r) = iota (ι ((translate-Arit arit) ⟨ r ∙ rev ν-flattenᵣ ⟩ ))
translate-Arit (spliₗ arit) = Pₗ $ translate-Arit arit 
translate-Arit (spliᵣ arit) = Pᵣ $ translate-Arit arit 
translate-Arit (arit₁ *N arit₂) = translate-Arit arit₁ *ₙ translate-Arit arit₂
translate-Arit (arit₁ *C arit₂) = translate-Arit arit₁ *  translate-Arit arit₂
translate-Arit (ω` arit₁ arit₂) = -ω (translate-Arit arit₁) (translate-Arit arit₂)
```


```agda
open import Matrix.Leveled.NatMon-Sum cplx
translate-Inp (compose inp₁ inp₂) = translate-Inp inp₂ ∘ translate-Inp inp₁
translate-Inp (copyOut` r₁ r₃ inp) =  reshape (up r₃) ∘ translate-Inp inp ∘ reshape (down r₁)
translate-Inp (part` s⊂p inp) = reshape (rev $ to-resh s⊂p) ∘ unnest ∘ map (translate-Inp inp) ∘ nest ∘ reshape (to-resh s⊂p)
translate-Inp (imap` x) = imap $ translate-Arit x
translate-Inp (mapSum` x) xs i = sum ((translate-Arit x) xs i ∘ ι)
```

We can then see what our fftn translates into

```agda
private variable
  ℓ : L
  
lemma₀ : ∀ {s : S zz} (xs : Ar (ι s) ℂ) (i : P (ι s)) →
         translate-Inp dft` xs i ≡ dft (reshape (down eq) xs) (i ⟨ up eq ⟩)
lemma₀ {ν x} xs (ι (ν x₁)) = refl


lemma₁ : ∀ {s : S (ss ℓ)} 
       → ∀ (FT-Inp : ∀ {p : S ℓ} → Inp translate-Ty (ι p))
       → ∀ (FT : ∀ {p : S ℓ} → Ar p ℂ → Ar p ℂ)
       → (∀ {s : S ℓ} → (xs ys : Ar s ℂ) → (∀ (i : P s) → xs i ≡ ys i) → (i : P s) → FT xs i ≡ FT ys i)
       → (∀ {p : S ℓ} (xs : Ar (ι p) ℂ) → ∀ i → translate-Inp FT-Inp xs i ≡ FT (reshape (down eq) xs) (i ⟨ up eq ⟩))
       → ∀ (xs : Ar s ℂ)
       → ∀ (i : P s)
       → translate-Inp (pre-ufft` FT-Inp) xs i ≡ pre-ufft FT (λ i j → twiddles (i ⟨ transpᵣ ⟩) j) xs i
lemma₁ {ℓ} {ι _} FT-Inp FT _ prf xs (ι i) = prf xs (ι i)
lemma₁ {ℓ} {s₁ ⊗ s₂} FT-Inp FT FT-cong prf xs (i₁ ⊗ i₂) = 
    lemma₁ FT-Inp FT FT-cong prf _ i₁ 
  ⊡ pre-ufft-cong FT-cong _ _ (λ j → *-comm _ _ ⊡ cong₂ _*_ (cong₂ -ω ? refl) (lemma₁ FT-Inp FT FT-cong prf _ i₂)) i₁

lemma₂ : ∀ {s : S (ss ℓ)} 
       → ∀ (FT-Inp : ∀ {p : S ℓ} → Inp translate-Ty (ι p))
       → ∀ (FT : ∀ {p : S ℓ} → Ar p ℂ → Ar p ℂ)
       → (∀ {s : S ℓ} → (xs ys : Ar s ℂ) → (∀ (i : P s) → xs i ≡ ys i) → (i : P s) → FT xs i ≡ FT ys i)
       → (∀ {p : S ℓ} (xs : Ar (ι p) ℂ) → ∀ i → translate-Inp FT-Inp xs i ≡ FT (reshape (down eq) xs) (i ⟨ up eq ⟩))
       → ∀ (xs : Ar s ℂ)
       → ∀ (i : P s)
       → translate-Inp (post-ufft` FT-Inp) xs i ≡ post-ufft FT (λ i j → twiddles i (j ⟨ transpᵣ ⟩)) xs i
lemma₂ {ℓ} {ι _} FT-Inp FT FT-cong prf xs (ι i) = prf xs (ι i)
lemma₂ {ℓ} {s₁ ⊗ s₂} FT-Inp FT FT-cong prf xs (i₁ ⊗ i₂) =
      lemma₂ FT-Inp FT FT-cong prf _ i₂
    ⊡ post-ufft-cong FT-cong _ _ (λ j → *-comm _ _ ⊡ cong₂ _*_ (cong₂ -ω ? ?) (lemma₂ FT-Inp FT FT-cong prf _ i₁)) i₂

lemma₃ : ∀ {s : S (ss (ss zz))}
       → ∀ (i : P (ι s))
       → i ⟨ up (CMᵗ ∙ rev transpᵣ )⟩ ≡ i ⟨ up eq ∙ (CMᵗ ∙ rev transpᵣ) ⟩ 
lemma₃ (ι i) = refl

lemma₄ : ∀ {s : S ℓ}
       → ∀ (i : P (ι s))
       → i ⟨ up CMᵗ ⟩ ≡ i ⟨ up eq ⟩ ⟨ CMᵗ ⟩
lemma₄ (ι i) = refl
--fftn` s = copyOut` eq (CMᵗ ∙ rev transpᵣ) (post-ufft` (copyOut` (rev transpᵣ) CMᵗ (pre-ufft` dft`))) 

prf : ∀ {s : S (ss (ss zz))}
    → ∀ (xs : Ar s ℂ)
    → ∀ (i  : P (ι s))
    → translate-Inp (fftn` s) (reshape (up eq) xs) i ≡ fftn xs (i ⟨ up eq ⟩)
prf xs i rewrite  
    lemma₃ i 
  | lemma₄ i = 
    lemma₂ _ _ ?
      (λ ys j → 
          cong (translate-Inp (pre-ufft` dft`) (λ i₁ → ys (ι (i₁ ⟨ rev transpᵣ ⟩)))) (lemma₄ j) 
        ⊡ lemma₁ dft` dft dft-cong lemma₀ (reshape (down (rev transpᵣ)) ys) (j ⟨ up eq ∙ CMᵗ ⟩)
      )
      xs 
      (i ⟨ up eq ∙ (CMᵗ ∙ rev transpᵣ) ⟩)


{-
rewrite  
  lemma₃ i = lemma₂ 
    (copyOut` (rev transpᵣ) CMᵗ (pre-ufft` dft`)) 
    (pre-ufft dft (λ i j → twiddles (i ⟨ transpᵣ ⟩) j))
    ((λ{ xs j → ? }))
    xs
    (i ⟨ up eq ∙ (CMᵗ ∙ rev transpᵣ) ⟩) ⊡ ?
    -}





    {-
prf {ι (ι (ν _))} _ (ι (ι (ι _))) = refl
prf {ι (s₁ ⊗ s₂)} xs (ι (ι (i₁ ⊗ i₂))) = ?
prf {s ⊗ s₁} xs i = ?
-}

```
