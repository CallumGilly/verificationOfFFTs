Here I define the translation from the DSL back to standard Agda I can then 
equate to my Agda implementation
```agda
{-# OPTIONS --allow-unsolved-metas #-}


open import ComplexNew
open import Real
open import Matrix.NatMon
open import Matrix.Leveled.NatMon-Change-Major 
--(spec : FFT-Specification cplx ℕ-Mon ℕ-CM)
module CodeGeneration.Translate-Agda (real : Real) (cplx : Cplx)  where
open import Function

open import Data.Nat renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Solver
open +-*-Solver
open import Data.Product hiding (map)

open Real.Real real renaming (+-*-isCommutativeRing to ℝ-+-*-isCommutativeRing; _+_ to _+ᵣ_; _*_ to _*ᵣ_; _-_ to _-ᵣ_)
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
translate-Ty R = ℝ
translate-Ty N = ℕ
translate-Ty (ix i) = P i
translate-Ty (x ⇒ y) = (translate-Ty x) → (translate-Ty y)
translate-Ty (x ⋆ y) = translate-Ty x × translate-Ty y
```

Given this we then need to create two translators - that for the set of in place 
operations and that for the set of arithmetic operations. 
```agda
translate-Arit : {τ : Ty} → Arit translate-Ty τ → translate-Ty τ
translate-Inp : ∀ {ℓ : L} {s : S ℓ} → Inp translate-Ty s (Scl C) → translate-Ty (ix s ⇒ C) → translate-Ty (ix s ⇒ C)
```

```agda
Pₗ : ∀ {l : L} {s p : S (ss l)} → P (s ⊗ p) → P s
Pₗ (i ⊗ _) = i

Pᵣ : ∀ {l : L} {s p : S (ss l)} → P (s ⊗ p) → P p
Pᵣ (_ ⊗ i) = i

toℂ : ℝ × ℝ → ℂ
toℂ (rl , im) = ?
fromℂ : ℂ → ℝ × ℝ
fromℂ x = ?

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

translate-Arit (toC aritᵣ aritᵢ) = toℂ $ (translate-Arit aritᵣ) , (translate-Arit aritᵢ)
translate-Arit (toRᵣ arit) = proj₁ $ fromℂ $ translate-Arit arit
translate-Arit (toRᵢ arit) = proj₂ $ fromℂ $ translate-Arit arit

translate-Arit (to-⋆ aritₗ aritᵣ) = (translate-Arit aritₗ) , (translate-Arit aritᵣ)
translate-Arit (⋆-proj₁ arit) = proj₁ (translate-Arit arit)
translate-Arit (⋆-proj₂ arit) = proj₂ (translate-Arit arit)

translate-Arit (arit₁ *R arit₂) = (translate-Arit arit₁) *ᵣ (translate-Arit arit₂)
translate-Arit (arit₁ +R arit₂) = (translate-Arit arit₁) +ᵣ (translate-Arit arit₂)
translate-Arit (arit₁ -R arit₂) = (translate-Arit arit₁) -ᵣ (translate-Arit arit₂)

translate-Arit (ωr` aritₙ aritᵢ) = proj₁ $ fromℂ $ -ω (translate-Arit aritₙ) (translate-Arit aritᵢ)
translate-Arit (ωi` aritₙ aritᵢ) = proj₂ $ fromℂ $ -ω (translate-Arit aritₙ) (translate-Arit aritᵢ)
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
       → ∀ (FT-Inp : ∀ {p : S ℓ} → Inp translate-Ty (ι p) (Scl C))
       → ∀ (FT : ∀ {p : S ℓ} → Ar p ℂ → Ar p ℂ)
       → (∀ {s : S ℓ} → (xs ys : Ar s ℂ) → (∀ (i : P s) → xs i ≡ ys i) → (i : P s) → FT xs i ≡ FT ys i)
       → (∀ {p : S ℓ} (xs : Ar (ι p) ℂ) → ∀ i → translate-Inp FT-Inp xs i ≡ FT (reshape (down eq) xs) (i ⟨ up eq ⟩))
       → ∀ (xs : Ar s ℂ)
       → ∀ (i : P s)
       → translate-Inp (pre-ufft` FT-Inp) xs i ≡ pre-ufft FT (λ i j → twiddles (i ⟨ transpᵣ ⟩) j) xs i
lemma₁ {ℓ} {ι _} FT-Inp FT _ prf xs (ι i) = prf xs (ι i)
lemma₁ {ℓ} {s₁ ⊗ s₂} FT-Inp FT FT-cong prf xs (i₁ ⊗ i₂) rewrite resh-length {_} {_} {transp s₁} transpᵣ = 
    lemma₁ FT-Inp FT FT-cong prf _ i₁ 
  ⊡ pre-ufft-cong FT-cong _ _ (λ j → *-comm _ _ ⊡ cong₂ _*_ (cong₂ -ω refl refl) (lemma₁ FT-Inp FT FT-cong prf _ i₂)) i₁

lemma₅ : ∀ {a b : ℕ} → a *ₙ b +ₙ a +ₙ b ≡ b *ₙ a +ₙ b +ₙ a 
lemma₅ {a} {b} = solve 2 (λ :a :b → :a :* :b :+ :a :+ :b := :b :* :a :+ :b :+ :a) refl a b 

lemma₂ : ∀ {s : S (ss ℓ)} 
       → ∀ (FT-Inp : ∀ {p : S ℓ} → Inp translate-Ty (ι p) (Scl C))
       → ∀ (FT : ∀ {p : S ℓ} → Ar p ℂ → Ar p ℂ)
       → (∀ {s : S ℓ} → (xs ys : Ar s ℂ) → (∀ (i : P s) → xs i ≡ ys i) → (i : P s) → FT xs i ≡ FT ys i)
       → (∀ {p : S ℓ} (xs : Ar (ι p) ℂ) → ∀ i → translate-Inp FT-Inp xs i ≡ FT (reshape (down eq) xs) (i ⟨ up eq ⟩))
       → ∀ (xs : Ar s ℂ)
       → ∀ (i : P s)
       → translate-Inp (post-ufft` FT-Inp) xs i ≡ post-ufft FT (λ i j → twiddles i (j ⟨ transpᵣ ⟩)) xs i
lemma₂ {ℓ} {ι _} FT-Inp FT FT-cong prf xs (ι i) = prf xs (ι i)
lemma₂ {ℓ} {s₁ ⊗ s₂} FT-Inp FT FT-cong prf xs (i₁ ⊗ i₂) rewrite resh-length {_} {_} {transp s₁} transpᵣ =
      lemma₂ FT-Inp FT FT-cong prf _ i₂
    ⊡ post-ufft-cong FT-cong _ _ (λ j → *-comm _ _ ⊡ cong₂ _*_ (cong₂ -ω (lemma₅ {length s₁} {_}) ?) (lemma₂ FT-Inp FT FT-cong prf _ i₁)) i₂

lemma₃ : ∀ {s : S (ss (ss zz))}
       → ∀ (i : P (ι s))
       → i ⟨ up (CMᵗ ∙ rev transpᵣ )⟩ ≡ i ⟨ up eq ∙ (CMᵗ ∙ rev transpᵣ) ⟩ 
lemma₃ (ι i) = refl

lemma₄ : ∀ {s : S ℓ}
       → ∀ (i : P (ι s))
       → i ⟨ up CMᵗ ⟩ ≡ i ⟨ up eq ⟩ ⟨ CMᵗ ⟩
lemma₄ (ι i) = refl


prf : ∀ {s : S (ss (ss zz))}
    → ∀ (xs : Ar s ℂ)
    → ∀ (i  : P (ι s))
    → translate-Inp (fftn` s) (reshape (up eq) xs) i ≡ fftn xs (i ⟨ up eq ⟩)
prf xs i rewrite  
    lemma₃ i 
  | lemma₄ i = 
    lemma₂ _ _ (λ xs′ ys′ xs≡ys j → pre-ufft-cong dft-cong (λ k₁ → xs′ (k₁ ⟨ rev transpᵣ ⟩)) (λ k₂ → ys′ (k₂ ⟨ rev transpᵣ ⟩)) (λ k → xs≡ys (k ⟨ rev transpᵣ ⟩)) (j ⟨ CMᵗ ⟩))
      (λ ys j → 
          cong (translate-Inp (pre-ufft` dft`) (λ i₁ → ys (ι (i₁ ⟨ rev transpᵣ ⟩)))) (lemma₄ j) 
        ⊡ lemma₁ dft` dft dft-cong lemma₀ (reshape (down (rev transpᵣ)) ys) (j ⟨ up eq ∙ CMᵗ ⟩)
      )
      xs 
      (i ⟨ up eq ∙ (CMᵗ ∙ rev transpᵣ) ⟩)
```
