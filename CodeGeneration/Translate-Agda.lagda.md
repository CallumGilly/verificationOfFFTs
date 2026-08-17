Here I define the translation from the DSL back to standard Agda I can then 
equate to my Agda implementation
```agda
open import ComplexNew
open import Matrix.NatMon
open import FFT.Leveled.Specification
open import Matrix.Leveled.NatMon-Change-Major 

module CodeGeneration.Translate-Agda (cplx : Cplx) (spec : FFT-Specification cplx ℕ-Mon ℕ-CM) where
open import Function

open import Data.Nat renaming (_*_ to _*ₙ_)

open Cplx cplx

open FFT-Specification spec
open import FFT.Leveled.Properties cplx ℕ-Mon ℕ-CM spec

open import Matrix.Leveled.Base ℕ-Mon
open import Matrix.Leveled.Reshape ℕ-Mon
open import Matrix.Leveled.SubShape ℕ-Mon

open import CodeGeneration.DSL
open import Relation.Binary.PropositionalEquality
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
translate-Inp : ∀ {ℓ : L} {s s′ : S ℓ} .(r : Reshape s s′) → Inp translate-Ty s s′ r → translate-Ty (ix s ⇒ C) → translate-Ty (ix s′ ⇒ C)
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
translate-Inp _ (compose r₁ inp₁ r₂ inp₂) = translate-Inp r₂ inp₂ ∘ translate-Inp r₁ inp₁
translate-Inp _ (view` r₁ inp) = reshape r₁ ∘ translate-Inp eq inp 
translate-Inp _ (copyOut` r₁ r₂ inp) = reshape (up r₂) ∘ translate-Inp (rev r₂ ∙ rev r₁) inp ∘ reshape (down r₁)
translate-Inp _ (part` s⊂p inp) = reshape (rev $ to-resh s⊂p) ∘ unnest ∘ map (translate-Inp eq inp) ∘ nest ∘ reshape (to-resh s⊂p)
translate-Inp _ (imap` x) = imap $ translate-Arit x
translate-Inp _ (mapSum` x) xs i = sum ((translate-Arit x) xs i ∘ ι)
```

We can then see what our fftn translates into

```agda
open import Data.Fin.Base
open import Data.Nat

{-
_ : ∀ xs i → translate-Inp eq (fftn` (ι (ι (ν 3) ⊗ ι (ν 4)))) xs i ≡ fftn xs i
_ = λ xs i → ?
-}

{-
_ : translate (fftn` (ι (ι (ν 3) ⊗ ι (ν 4)) ⊗ (ι (ι (ν 5) ⊗ ι (ν 6))))) ≡ fftn 
_ = ?

prf : ∀ {s : S (ss (ss zz))}
    → ∀ (xs : Ar s ℂ)
    → ∀ (i  : P s)
    → translate (fftn` s) xs i ≡ fftn xs i
prf {ι (ι s)} xs (ι (ι i)) = refl
prf {ι (s ⊗ s₁)} xs (ι (i ⊗ i₁)) = ?
prf {s ⊗ s₁} xs i = ?
-}
```
