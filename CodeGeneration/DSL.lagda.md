Here I define the DSL with which I can model the FFT. 
I should then be able to define a transpiler from an implementation in the DSL,
to Agda (to give semantics), and to `C` (to generate for performance).

```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Nat
module CodeGeneration.DSL (LANES : ℕ) where
open import Matrix.Mon
open import Matrix.NatMon

open import Matrix.Leveled.Base ℕ-Mon
open import Matrix.Leveled.Reshape ℕ-Mon
open import Matrix.Leveled.Change-Major ℕ-Mon
open import Matrix.Leveled.SubShape ℕ-Mon renaming (id to sid)
open import Matrix.Leveled.NatMon-Change-Major

open import Data.Fin renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality
open import Function.Base hiding (_∋_)

_⊡_ = trans
```
```agda
open Change-Major ℕ-CM
```

Technically I don't actually need a dependency on FFT yet - it's only needed 
when I give the DSL semantics.
```agda
-- open import FFT.Leveled ? ℕ-Mon
```

# Types

For now I will just deal with Complex as a type - this needs to be changed to ℝ × ℝ
but this is probably best left till later (have done it before and should be 
an easy conversion).
```agda
infixr 25 _⇒_
infixr 30 _⋆_
data Ty : Set where
  C : Ty
  R : Ty
  N : Ty
  ix : {l : L} → S l → Ty
  _⇒_ : Ty → Ty → Ty
  _⋆_ : Ty → Ty → Ty
  ℝ : Ty

private
  variable
    l : L
    s p : S l
    τ δ σ : Ty
```

For these basic types, we can then define arrays. This definition (and that 
above for `ix`) doesn't do anything special yet for levels, but just parses them 
in the same way we have before.
```agda
ar : ∀ {l : L} → S l → Ty → Ty
ar s X = ix s ⇒ X
```
We can then define two subsets of `Ty`:
The set of numeric types (Complex and Arrays)
```agda
data Scalar : Ty → Set where
  C : Scalar C
  R : Scalar R
  N : Scalar N
  --- This is a lie, but a good one ---
  ℝ : Scalar ℝ

data Num : Ty → Set where
  Scl : Scalar τ → Num τ
  _⋆_ : Num τ →  Num σ → Num (τ ⋆ σ)
  --arr : ∀ {s : S l} → Num τ → Num (ix s ⇒ τ)
```
The set of numeric types and applications which return numeric types
```agda
data FNum : Ty → Set where
  num : Num τ → FNum τ
  fun : Num τ → FNum σ → FNum (τ ⇒ σ)
```

```agda
Id : Set
Id = ?

record ConPair : Set where
  constructor [_,_]
  field
    { ConPair-τ }  : Ty
    ConPair-Num    : Num ConPair-τ
    { ConPair-ℓ }  : L
    ConPair-Shape  : S ConPair-ℓ
open ConPair

infixr 7 _◃_ 
infixr 7 _◂_ 
-- I think I need to extend context to allow it to carry scalars as well as arrays
-- What if i did the smart thing and carried num with the option of ix s ⇒ Scl τ...
data Ctxt : Set where
  ⊘ : Ctxt
  _◃_ : ConPair → Ctxt → Ctxt

variable
  Γ Δ Φ : Ctxt

data _∋_ : Ctxt → ConPair → Set where
  here  : ∀ {x   : ConPair} {Γ : Ctxt} →         (x ◃ Γ) ∋ x
  there : ∀ {x y : ConPair} {Γ : Ctxt} → Γ ∋ x → (y ◃ Γ) ∋ x

data All (P : ConPair → Set) : Ctxt → Set where 
  ⊘   : All P ⊘
  _◂_ : ∀ {x : ConPair} → P x → All P Γ → All P (x ◃ Γ)

data NonEmpty : Ctxt → Set where
  ne : ∀ {x : ConPair} → {Γ : Ctxt} → NonEmpty (x ◃ Γ)

allTys : Ctxt → Ty → Ty
allTys ⊘ σ = σ
allTys (conPair ◃ Γ) σ = (ConPair-τ conPair) ⇒ (allTys Γ σ)

_ : ∀ {τ : Ty} {x y z : ConPair} → allTys (x ◃ y ◃ z ◃ ⊘) τ ≡ (ConPair-τ x) ⇒ ((ConPair-τ y) ⇒ ((ConPair-τ z) ⇒ τ))
_ = refl

Ctxt-to-⋆ : (Γ : Ctxt) → NonEmpty Γ → Ty
Ctxt-to-⋆ (x ◃ ⊘)         ne = ConPair-τ x
Ctxt-to-⋆ (x ◃ Γ@(_ ◃ _)) ne = ConPair-τ x ⋆ (Ctxt-to-⋆ Γ ne)

_ : ∀ {x y z : ConPair} → Ctxt-to-⋆ (x ◃ y ◃ z ◃ ⊘) ne ≡ (ConPair-τ x) ⋆ ((ConPair-τ y) ⋆ (ConPair-τ z))
_ = refl


mapCtxt : Ctxt → (ConPair → ConPair) → Ctxt
mapCtxt ⊘ f = ⊘
mapCtxt (x ◃ Γ) f = f x ◃ mapCtxt Γ f

module _ {P : ConPair → Set} where
  open import Data.Product

  mapCtxtP : (Γ : Ctxt) → All P Γ → ((Σ ConPair P) → ConPair) → Ctxt
  mapCtxtP ⊘ ⊘ _ = ⊘
  mapCtxtP (x ◃ Γ) (p ◂ all) f = f (x , p) ◃ mapCtxtP Γ all f

-- Order preserving
data _⊆ᶜ_ : Ctxt → Ctxt → Set where
  empt : ⊘ ⊆ᶜ Γ
  drop : ∀ {x : ConPair} → Δ ⊆ᶜ Γ →      Δ  ⊆ᶜ (x ◃ Γ)
  here : ∀ {x : ConPair} → Δ ⊆ᶜ Γ → (x ◃ Δ) ⊆ᶜ (x ◃ Γ)

module _ (F : ConPair → ConPair) where
  data _⊆ᵖ_ : Ctxt → Ctxt → Set where
    empt : ⊘ ⊆ᵖ Γ
    drop : ∀ {x : ConPair} → Δ ⊆ᵖ Γ →        Δ  ⊆ᵖ (x ◃ Γ)
    here : ∀ {x : ConPair} → Δ ⊆ᵖ Γ → (F x ◃ Δ) ⊆ᵖ (x ◃ Γ)


open import Data.Product hiding (curry; uncurry) renaming (_,_ to _,ₚ_)
{-
module _ (P : ConPair → Set) (F : (x : ConPair) → P x → Σ ConPair P) where
  data SubPF : (Γ : Ctxt) → (All P Γ) → Ctxt → Set where
    empt : SubPF ⊘ ⊘ Γ
    drop : ∀ {x : ConPair} 
         → (all : All P Δ) 
         → SubPF Δ all Γ 
         → SubPF Δ all (x ◃ Γ)
    here : ∀ {x : ConPair} 
         → (∀Δ : All P Δ) 
         → (xₚ : P x) 
         → SubPF Δ ∀Δ Γ 
         → SubPF (F x xₚ .proj₁ ◃ Δ) (F x xₚ .proj₂ ◂ ∀Δ) (x ◃ Γ)
-} 


```

# The DSL
Given the basic typing system, I can now create the DSL.

Here I actually make use of two parts for the DSL:
- The first comprises the set of arithmetic operations.
- The second comprises the set of in place operations.

# The set of arithmetic operations
I first create the set of arithmetic operations. 

I initially made this with "Contexts" where variables where referenced via their
De-Bruijn index, but I realised this is not what I needed context to be when I 
went to create the Agda translator.
```agda
-- This doesn't quite work as my Ctxt is restricted to arrays only.
-- I could generalise contexts to something like [ConPair | Num τ]
-- data CtxtArit (Γ : Ctxt) : Ty → Set where

data Arit (Sem : Ty → Set) : Ty → Set where
  var   : Sem τ → Arit Sem τ
  lam   : (Sem τ → Arit Sem σ) → Arit Sem (τ ⇒ σ)
  app   : Arit Sem (τ ⇒ σ) → Arit Sem τ → Arit Sem σ

  sizeN : Arit Sem (ix s) → Arit Sem N
  posiN : Arit Sem (ix s) → Reshape p s → Arit Sem N
  spliₗ : Arit Sem (ix (s ⊗ p)) → Arit Sem (ix s)
  spliᵣ : Arit Sem (ix (s ⊗ p)) → Arit Sem (ix p)

  _*N_ : Arit Sem N → Arit Sem N → Arit Sem N 

  _*C_ : Arit Sem C → Arit Sem C → Arit Sem C 
  ω`   : Arit Sem N → Arit Sem N → Arit Sem C

  toC  : Arit Sem R → Arit Sem R → Arit Sem C
  toRᵣ : Arit Sem C → Arit Sem R
  toRᵢ : Arit Sem C → Arit Sem R

  to-⋆     : Arit Sem τ → Arit Sem σ → Arit Sem (τ ⋆ σ)
  ⋆-proj₁ : Arit Sem (τ ⋆ σ) → Arit Sem τ
  ⋆-proj₂ : Arit Sem (τ ⋆ σ) → Arit Sem σ
  
  _*R_ : Arit Sem R → Arit Sem R → Arit Sem R 
  _+R_ : Arit Sem R → Arit Sem R → Arit Sem R 
  _-R_ : Arit Sem R → Arit Sem R → Arit Sem R 

  repeat       : (n : ℕ) → Arit Sem R → Arit Sem ℝ

  SIMD-*R      : {n : ℕ} → Arit Sem ℝ → Arit Sem ℝ → Arit Sem ℝ
  SIMD-+R      : {n : ℕ} → Arit Sem ℝ → Arit Sem ℝ → Arit Sem ℝ
  SIMD--R      : {n : ℕ} → Arit Sem ℝ → Arit Sem ℝ → Arit Sem ℝ
  {-
    Here we can just use to-⋆ to make a pair of ℝ

  SIMD-to-⋆    : {n : ℕ} → Arit Sem (τ ◎ n) → Arit Sem (σ ◎ n) → Arit Sem (τ ⋆ σ ◎ n)
  SIMD-⋆-proj₁ : {n : ℕ} → Arit Sem (τ ⋆ σ ◎ n)  → Arit Sem (τ ◎ n)
  SIMD-⋆-proj₂ : {n : ℕ} → Arit Sem (τ ⋆ σ ◎ n)  → Arit Sem (σ ◎ n)
  -}

  ωr`  : Arit Sem N → Arit Sem N → Arit Sem R
  ωi`  : Arit Sem N → Arit Sem N → Arit Sem R
```

```agda  

mult : {Sem : Ty → Set} (a b c d : Arit Sem R) → Arit Sem (R ⋆ R)
mult a b c d = to-⋆ ((a *R c) -R (b *R d)) ((a *R d) +R (b *R c)) 

{-
SIMD-mult : {n : ℕ} {Sem : Ty → Set} (a b c d : Arit Sem (R ◎ n)) → Arit Sem (R ⋆ R ◎ n)
SIMD-mult a b c d = SIMD-to-⋆ (SIMD--R (SIMD-*R a c) (SIMD-*R b d)) (SIMD-+R (SIMD-*R a d) (SIMD-*R b c))
-}

curry : ∀ {Sem : Ty → Set} → ∀ { X : Set } → (Arit Sem (R ⋆ R) → X) → (Arit Sem R → Arit Sem R → X)
curry f r i = f (to-⋆ r i)

{-
SIMD-curry : ∀ {n : ℕ} {Sem : Ty → Set} → ∀ { X : Set } → (Arit Sem (R ⋆ R ◎ n) → X) → (Arit Sem (R ◎ n) → Arit Sem (R ◎ n) → X)
SIMD-curry f r i = f (SIMD-to-⋆ r i)
-}

uncurry : ∀ {Sem : Ty → Set} → ∀ { X : Set } → (Arit Sem R → Arit Sem R → X) → (Arit Sem (R ⋆ R) → X)
uncurry f x = f (⋆-proj₁ x) (⋆-proj₂ x)

{-
SIMD-uncurry : ∀ {n : ℕ} {Sem : Ty → Set} → ∀ { X : Set } → (Arit Sem (R ◎ n) → Arit Sem (R ◎ n) → X) → (Arit Sem (R ⋆ R ◎ n) → X)
SIMD-uncurry f x = f (SIMD-⋆-proj₁ x) (SIMD-⋆-proj₂ x)
-}

{-
ω` : ∀ {Sem : Ty → Set} → Arit Sem N → Arit Sem N → Arit Sem C
ω` n j = toC (ωr` n j) (ωi` n j)
-}
{-
_*C_ : ∀ {Sem} → Arit Sem C → Arit Sem C → Arit Sem C 
x *C′ y =
  let a = toRᵣ x in
  let b = toRᵢ x in
  let c = toRᵣ y in
  let d = toRᵢ y in
  toC ((a *R c) -R (b *R d)) ((a *R d) +R (b *R c))
-}

--let′_=′_in′_ : ∀ {Sem} → (Sem τ) → (Arit Sem τ) → Arit Sem σ → Arit Sem σ
--let′_=′_in′_ nm x y = app ? ?


infix 1 lam
syntax lam (λ x → e) = `λ x ⇒ e
```

Here I check that I have setup the lambda calculi correctly by ensuring I can 
represent the SKI operators
```agda
module _ where
  private variable
    Sem : Ty → Set

  I` : Arit Sem (τ ⇒ τ)
  I` = lam (λ x → var x)

  K` : Arit Sem (τ ⇒ σ ⇒ τ)
  K` = lam λ x → lam λ y → var x
  -- 
  S` : Arit Sem ((σ ⇒ δ ⇒ τ) ⇒ (σ ⇒ δ) ⇒ σ ⇒ τ)
  S` = `λ x ⇒ `λ y ⇒ `λ z ⇒ app (app (var x) (var z)) (app (var y) (var z))
```

# The set of in place operations

We can then define the set of In-Place operations `Inp`.

We restrict these to currently operate over one shape level `l`
```agda
module _ where
  infixl 2 _>>>_
```

Sure the below would work and would allow us to refine to SIMD, but is it too 
strict. If we want to be able to use simd operations when we ⟨ swap ⟩ we would 
require s ≡ lanes. This would mean we would be fixing the radix of the fft to 
lanes as opposed to a multiple of

```agda
  --data IsSimd′ : {ℓ : L} (s : S ℓ) → Set where
  --  base : ∀ {n : ℕ} → IsSimd′ (ν (n *ₙ lane))

  {-
  data IsSimd : {ℓ : L} (s : S ℓ) → Set where
    base : ∀ {s : S zz} → IsSimd ((ι s) ⊗ ι lanes)
    down : ∀ {ℓ : L} {s : S ℓ} → IsSimd s → IsSimd (ι s)
    comp : ∀ {ℓ : L} {s p : S (ss ℓ)} → IsSimd s → IsSimd p → IsSimd (s ⊗ p)
  -}

  data NewInp (Sem : Ty → Set) : (Γ Δ : Ctxt) → Set where
    compose : NewInp Sem Γ Φ
            → NewInp Sem Φ Δ
            → NewInp Sem Γ Δ

    -- Generalised imap where every operation can also access the elements at 
    -- the simultanious operations (Meaning we will need to make use of temporary variables)
    imap` : ∀ {Γ Δ : Ctxt}
          → Δ ⊆ᶜ Γ --- This should really be ⊆ and flipped ⊢ feels wrong in this context (pun intended)
          → ∀ {ℓ : L} (s : S ℓ)
          -- → ( ne : NonEmpty Δ )
          → All (Reshape s ∘ ConPair-Shape) Δ
          → All (λ conPair → Arit Sem (allTys Δ ((ix (ConPair-Shape conPair)) ⇒ ConPair-τ conPair))) Δ
          -- Annoyingly, this is acceptable for map, but not acceptable for imap 
          -- where each ar could be of a different shape
          --→ Arit Sem (allTys Δ (Ctxt-to-⋆ Δ ne))
          --→ _⊆ᵖ_ (λ conPair → Reshape s (ConPair-Shape conPair)) Δ Γ 
          → NewInp Sem Γ Γ

    mapSum` : ∀ {Γ Δ : Ctxt} 
            → Δ ⊆ᶜ Γ
            → ∀ {u : ℕ}
            → All (Reshape (ι (ν u)) ∘ ConPair-Shape) Δ
            --→ ∀ {Sem : Ty → Set}
            → All (λ conPair → Arit Sem (allTys Δ (ix (ι (ν u)) ⇒ ix (ι (ν u)) ⇒ ConPair-τ conPair))) Δ
            → NewInp Sem Γ Γ

    copyOut` : {Γ Δ : Ctxt} 
             → _⊆ᵖ_ (λ conPair → [ (ConPair-Num conPair) , s ] ) Δ Γ
             → (s : S (ss l))
             → All (λ conPair → Reshape s (ConPair-Shape conPair)) Δ
             → All (λ conPair → Reshape (ConPair-Shape conPair) s) Δ
             → NewInp Sem Δ Δ
             → NewInp Sem Γ Γ
    
    -- The easiest form of part is where every Ar in Δ is of the same Shape
    part` : ∀ {Γ Δ : Ctxt}
          --→ Δ ⊆ᶜ Γ
          → {ℓ : L} (s p : S (ss ℓ))
          --→ (s⊂p : s ⊂ p)
          --→ (sameS : All (λ conPair → Σ (ConPair-ℓ conPair ≡ (ss ℓ)) λ{refl → s ≡ ConPair-Shape conPair}) Δ)
          --→ let Φ = mapCtxtP Δ sameS λ{(conPair ,ₚ refl ,ₚ refl) → [ (ConPair-Num conPair) , (inv-⊂ s⊂p) ]} in NewInp Sem Φ Φ
          -- Pain to read, but:
            -- Give me a: Shape, which has a reshape to our shape of recursion, and is a subshape of the arrays shape 
            -- And an imap which operates over the inverse of this sub
          → (reshapeableS : All (λ conPair → ∃ λ p → Σ (Reshape s p) λ r → p ⊂ ConPair-Shape conPair) Δ)
          → let Φ = mapCtxtP Δ reshapeableS λ{(conPair ,ₚ _ ,ₚ _ ,ₚ sub) → [ ConPair-Num conPair , (inv-⊂ sub) ] } in NewInp Sem Φ Φ
          → NewInp Sem Γ Γ
    {-
    -- I need to generate a context from Δ, where every shape is a subshape of 
    --
    -- We can flip this on it's head and say that we iterate over S, and say
    -- how s is a subshape of each of the shapes in the context
    -- Then our inverse of s ⊂ conShape is the new shape in the context :)
    part` : ∀ {Γ Δ : Ctxt}
          → Γ ⊢ Δ
          → {ℓ : L} (s : S ℓ)
          → (subs : All (λ conPair → Σ (ConPair-ℓ conPair ≡ ℓ) λ{refl → s ⊂ (ConPair-Shape conPair)}) Δ) 
          → let a = mapCtxt Δ (λ conPair → [ (ConPair-Num conPair) , (let a = s ⊂ ? in ?) ] ) in ?
          → NewInp Sem ? ?
          → NewInp Sem Γ Γ
    -}
 


  data Inp (Sem : Ty → Set) : {l : L} (s : S l) {τ : Ty} (num : Num τ) → Set₁ where
    compose  : ∀ {s₁ : S l} {τ : Ty} {num : Num τ}
             → Inp Sem s₁ num
             → Inp Sem s₁ num
             → Inp Sem s₁ num
    copyOut` : {s : S (ss l)} 
             → {p : S (ss l)}
             → {τ : Ty} {num : Num τ}
             → (r₁ : Reshape s p) 
             → (r₂ : Reshape p s) 
             → Inp Sem p num
             → Inp Sem (ι s) num
    part`    : ∀ {s p : S (ss l)} 
             → {τ : Ty} {num : Num τ}
             → (s⊂p : s ⊂ p) 
             → Inp Sem (inv-⊂ s⊂p) num
             → Inp Sem p num
    imap`    : ∀ {τ : Ty} {num : Num τ} 
             → Arit Sem (ix s ⇒ τ ⇒ τ) → Inp Sem s num
    mapSum`  : ∀ {u : ℕ} 
             → ∀ {τ : Ty} {num : Num τ}
             → Arit Sem ((ar (ι (ν u)) τ) ⇒ ix (ι (ν u)) ⇒ ix (ι (ν u)) ⇒ τ) 
             → Inp Sem (ι (ν u)) num

    -- But what do we want to do re - ℝ ⋆ ℝ
    vec   : ∀ {s : S _}
          → Inp Sem (s ⊗ (ι (ν LANES))) (Scl R)
          → Inp Sem s (Scl ℝ)

    unvec : ∀ {s : S _}
          → Inp Sem s (Scl ℝ)
          → Inp Sem (s ⊗ (ι (ν LANES))) (Scl R)
  
  _>>>_ : ∀ {Sem : Ty → Set} 
        → ∀ {l : L}
        → ∀ {s : S l}
        → ∀ {τ : Ty} {num : Num τ} 
        → Inp Sem s num → Inp Sem s num → Inp Sem s num
  _>>>_ {Sem} {_} {s} e₁ e₂ = compose e₁ e₂

  vec-⋆ : ∀ {Sem : Ty → Set} {s : S _}
        → Inp Sem (s ⊗ (ι (ν LANES))) (Scl R ⋆ Scl R)
        → Inp Sem s (Scl ℝ ⋆ Scl ℝ)
  vec-⋆ {Sem} {s} inp = ?
```

Within these in place operations, we can then represent twiddles...


```agda
twid` : {s s′ p p′ : S (ss l)} {Sem : Ty → Set} → (r₁ : Reshape s′ s) → (r₂ : Reshape p′ p) → Inp Sem (s ⊗ p) (Scl C)
twid` {l} {s} {s′} {p} {p′} r₁ r₂ = 
      imap`
        (`λ i ⇒ `λ x ⇒ 
          (var x) *C
          ω` 
            (sizeN $ var i) 
            ((posiN (spliₗ $ var $ i) r₁) *N (posiN (spliᵣ $ var $ i) r₂))
        )

-- This is grim, can I change this to allow me to give a Arit for (R ⋆ R)...
Ntwid` : {s s′ p p′ : S (ss l)} {Sem : Ty → Set} → (r₁ : Reshape s′ s) → (r₂ : Reshape p′ p) → NewInp Sem ([ Scl R , (s ⊗ p) ] ◃ [ Scl R , (s ⊗ p) ] ◃ ⊘) _
Ntwid` {l} {s} {s′} {p} {p′} {Sem} r₁ r₂ = 
      imap` 
        (here (here empt)) 
        {ss l} 
        (s′ ⊗ p′) 
        ((r₁ ⊕ r₂) ◂ (r₁ ⊕ r₂) ◂ ⊘) 
        ( (`λ xᵣ ⇒ `λ xᵢ ⇒ `λ i ⇒ 
            let ωᵣ = ωr` (sizeN $ var i) ((posiN (spliₗ $ var $ i) r₁) *N (posiN (spliᵣ $ var $ i) r₂)) in
            let ωᵢ = ωi` (sizeN $ var i) ((posiN (spliₗ $ var $ i) r₁) *N (posiN (spliᵣ $ var $ i) r₂)) in
            ⋆-proj₁ (mult (var xᵣ) (var xᵢ) ωᵣ ωᵢ)
          )
        ◂ (`λ xᵣ ⇒ `λ xᵢ ⇒ `λ i ⇒ 
            let ωᵣ = ωr` (sizeN $ var i) ((posiN (spliₗ $ var $ i) r₁) *N (posiN (spliᵣ $ var $ i) r₂)) in
            let ωᵢ = ωi` (sizeN $ var i) ((posiN (spliₗ $ var $ i) r₁) *N (posiN (spliᵣ $ var $ i) r₂)) in
            ⋆-proj₂ (mult (var xᵣ) (var xᵢ) ωᵣ ωᵢ)
          )
        ◂ ⊘
        )

{-
Ntwid` {l} {s} {s′} {p} {p′} {Sem} r₁ r₂ =
      imap` 
        (here (here empt))
        {ss l}
        (s′ ⊗ p′)
        ne
        ((r₁ ⊕ r₂) ◂ (r₁ ⊕ r₂) ◂ ⊘)
        ?
-}

Rtwid` : {s s′ p p′ : S (ss l)} {Sem : Ty → Set} → (r₁ : Reshape s′ s) → (r₂ : Reshape p′ p) → Inp Sem (s ⊗ p) ((Scl R) ⋆ (Scl R))
Rtwid` {l} {s} {s′} {p} {p′} r₁ r₂ = 
      imap`
        (`λ i ⇒ `λ x ⇒ 
            let ωᵣ = ωr` (sizeN $ var i) ((posiN (spliₗ $ var $ i) r₁) *N (posiN (spliᵣ $ var $ i) r₂)) in
            let ωᵢ = ωi` (sizeN $ var i) ((posiN (spliₗ $ var $ i) r₁) *N (posiN (spliᵣ $ var $ i) r₂)) in
          (uncurry mult (var x)) ωᵣ ωᵢ
        )
```

```agda
dft` : ∀ {s : S zz} {Sem : Ty → Set} → Inp Sem (ι s) (Scl C)
dft` {ν u} = mapSum` {u = u} $ `λ xs ⇒ `λ j ⇒ `λ k ⇒ (app (var xs) (var k)) *C (ω` (sizeN (var j)) ((posiN (var k) eq) *N (posiN (var j) eq)))

Rdft` : ∀ {s : S zz} {Sem : Ty → Set} → Inp Sem (ι s) ((Scl R) ⋆ (Scl R))
Rdft` {ν u} = mapSum` {u = u} $ `λ xs ⇒ `λ j ⇒ `λ k ⇒ 
    let ωᵣ  = ωr` (sizeN (var j)) ((posiN (var k) eq) *N (posiN (var j) eq)) in
    let ωᵢ  = ωi` (sizeN (var j)) ((posiN (var k) eq) *N (posiN (var j) eq)) in
    (uncurry mult (app (var xs) (var k))) ωᵣ ωᵢ

NewRdft` : ∀ {s : S zz} {Sem : Ty → Set} → NewInp Sem ([ Scl R , s ] ◃ [ Scl R , s ] ◃ ⊘) _
NewRdft` {ν u} {Sem} = mapSum` {_} {_} {_} (here (here empt)) {u} (down eq ◂ down eq ◂ ⊘) (? ◂ ? ◂ ⊘)

{-
-- Should do N dft's in parallel
SIMDdft` : ∀ {s : S zz} {Sem : Ty → Set} → {n : ℕ} → Inp Sem (ι s) (((Scl R) ⋆ (Scl R)) ◎ n)
SIMDdft` {ν u} {Sem} = mapSum` {u = u} $ `λ xs ⇒ `λ j ⇒ `λ k ⇒
    let ωᵣ  = ωr` (sizeN (var j)) ((posiN (var k) eq) *N (posiN (var j) eq)) in
    let ωᵢ  = ωi` (sizeN (var j)) ((posiN (var k) eq) *N (posiN (var j) eq)) in
    (SIMD-uncurry SIMD-mult (app (var xs) (var k))) (repeat _ ωᵣ) (repeat _ ωᵢ)
    -}
```

# Defining the FFT

The return value of the standard implementation of the FFT over will return the 
input shape transposed because the last stage of the recursive step swaps the input.
Swaps are expensive and so we instead use the UFFT which push's all swaps to 
either the end or the start of the computation. If the input is given transposed,
I call it `pre-ufft`, if the output needs to be transposed, I call it `post-ufft`.
Both are defined here

```agda
pre-ufft`  : ∀ {Sem : Ty → Set} → ∀ (lower-ft : ∀ {p : S l} → Inp Sem (ι p) (Scl C))
          → ∀ {s : S (ss l)} → Inp Sem s (Scl C)
pre-ufft` lower-ft {ι s} = lower-ft
pre-ufft` lower-ft {s ⊗ p} = part` (le sid) (pre-ufft` lower-ft {p})       -- Left ufft
                             >>> twid` {_} {s} {transp s} {p} {p} transpᵣ eq  -- Twiddles 
                             >>> part` (ri sid) (pre-ufft` lower-ft {s})       -- Right ufft

Rpre-ufft`  : ∀ {Sem : Ty → Set} → ∀ (lower-ft : ∀ {p : S l} → Inp Sem (ι p) ((Scl R) ⋆ (Scl R)))
          → ∀ {s : S (ss l)} → Inp Sem s ((Scl R) ⋆ (Scl R))
Rpre-ufft` lower-ft {ι s} = lower-ft
Rpre-ufft` lower-ft {s ⊗ p} = part` (le sid) (Rpre-ufft` lower-ft {p})       -- Left ufft
                             >>> Rtwid` {_} {s} {transp s} {p} {p} transpᵣ eq  -- Twiddles 
                             >>> part` (ri sid) (Rpre-ufft` lower-ft {s})       -- Right ufft
```
The output of the following `post-ufft` would need to be transposed then 
change majored to be correct.
```agda
post-ufft` : ∀ {Sem : Ty → Set} → ∀ (lower-ft : ∀ {p : S l} → Inp Sem (ι p) (Scl C))
          → ∀ {s : S (ss l)} → Inp Sem s (Scl C)
post-ufft` lower-ft {ι s} = lower-ft 
post-ufft` lower-ft {s ⊗ p} = part` (ri sid) (post-ufft` lower-ft {s})     -- Right ufft
                              >>> twid` {_} {s} {s} {p} {transp p} eq transpᵣ -- Twiddles 
                              >>> part` (le sid) (post-ufft` lower-ft {p})     -- Left ufft

Rpost-ufft` : ∀ {Sem : Ty → Set} → ∀ (lower-ft : ∀ {p : S l} → Inp Sem (ι p) ((Scl R) ⋆ (Scl R)))
          → ∀ {s : S (ss l)} → Inp Sem s ((Scl R) ⋆ (Scl R))
Rpost-ufft` lower-ft {ι s} = lower-ft 
Rpost-ufft` lower-ft {s ⊗ p} = part` (ri sid) (Rpost-ufft` lower-ft {s})     -- Right ufft
                              >>> Rtwid` {_} {s} {s} {p} {transp p} eq transpᵣ -- Twiddles 
                              >>> part` (le sid) (Rpost-ufft` lower-ft {p})     -- Left ufft
```


We can then define `fftn` in our DSL.

```agda
fftn` : ∀ {Sem : Ty → Set} → (s : S (ss (ss zz))) → Inp Sem (ι s) (Scl C)
fftn` s = copyOut` eq (CMᵗ ∙ rev transpᵣ) (post-ufft` (copyOut` (rev transpᵣ) CMᵗ (pre-ufft` dft`))) 

Rfftn` : ∀ {Sem : Ty → Set} → (s : S (ss (ss zz))) → Inp Sem (ι s) ((Scl R) ⋆ (Scl R))
Rfftn` s = copyOut` eq (CMᵗ ∙ rev transpᵣ) (Rpost-ufft` (copyOut` (rev transpᵣ) CMᵗ (Rpre-ufft` Rdft`))) 
```
