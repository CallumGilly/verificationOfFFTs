Here I define the translation from the DSL back to standard Agda I can then 
equate to my Agda implementation
```agda
open import ComplexNew
open import Matrix.NatMon
open import FFT.Leveled.Specification
open import Matrix.Leveled.NatMon-Change-Major 

module CodeGeneration.Translate-Agda (cplx : Cplx) (spec : FFT-Specification cplx ℕ-Mon ℕ-CM) where
open import Function

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
```agda
translate-Ty : Ty → Set
translate-Ty C = ℂ
translate-Ty (ix i) = P i
translate-Ty (x ⇒ y) = (translate-Ty x) → (translate-Ty y)

```



```agda

translate : ∀ {ITy OTy : Ty} → Inp ITy OTy → translate-Ty ITy → translate-Ty OTy
translate (ins₁ >>> ins₂) = translate ins₂ ∘ translate ins₁ 
translate dft` x = dft x
translate (copy` r) x = reshape r x
translate (part` {ss l} s⊂p ins ) = let r = to-resh s⊂p in reshape (rev r) ∘ unnest ∘ map (translate ins) ∘ nest ∘ reshape r
translate (twid` r₁ r₂) xs i@(i₁ ⊗ i₂) = xs i * twiddles (i₁ ⟨ r₁ ⟩) (i₂ ⟨ r₂ ⟩)

```

We can then see what our fftn translates into

```agda

_ : ∀ xs i → translate (fftn` (ι (ι (ν 3)))) xs i ≡ fftn xs i
_ = λ{xs (ι (ι (ν i))) → refl}

_ : translate (fftn` (ι (ι (ν 3) ⊗ ι (ν 4)))) ≡ fftn 
_ = ?

_ : translate (fftn` (ι (ι (ν 3) ⊗ ι (ν 4)) ⊗ (ι (ι (ν 5) ⊗ ι (ν 6))))) ≡ fftn 
_ = ?

prf : ∀ {s : S (ss (ss zz))}
    → ∀ (xs : Ar s ℂ)
    → ∀ (i  : P s)
    → translate (fftn` s) xs i ≡ fftn xs i
prf {ι (ι s)} xs (ι (ι i)) = refl
prf {ι (s ⊗ s₁)} xs (ι (i ⊗ i₁)) = ?
prf {s ⊗ s₁} xs i = ?

```
