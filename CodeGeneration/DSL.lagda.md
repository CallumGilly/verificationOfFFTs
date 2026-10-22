Here I define the DSL with which I can model the FFT. 
I should then be able to define a transpiler from an implementation in the DSL,
to Agda (to give semantics), and to `C` (to generate for performance).

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module CodeGeneration.DSL where
open import Matrix.Mon
open import Matrix.NatMon

open import Matrix.Leveled.Base ℕ-Mon
open import Matrix.Leveled.Reshape ℕ-Mon
open import Matrix.Leveled.Change-Major ℕ-Mon
open import Matrix.Leveled.SubShape ℕ-Mon renaming (id to sid)
open import Matrix.Leveled.NatMon-Change-Major

open import Data.Nat
open import Data.Fin renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality
open import Function.Base

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
  _⋆_ : Ty → Ty → Ty -- Can I use this for SIMD Then????
  -- Or do I want something like:
  --SR : Ty
  -- Using ⋆ may break refinement of C to R ⋆ R
  -- Using SR means that we don't have clear semantics?
  -- I COULD add a new × which is also Scalar?
  _◎_ : Ty → ℕ → Ty

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

data Num : Ty → Set where
  Scl : Scalar τ → Num τ
  --Simd : Scalar τ → (n : ℕ) → Num (repeat n τ)
  _◎_ : Num τ → (n : ℕ) → Num (τ ◎ n)
  _⋆_ : Num τ →  Num σ → Num (τ ⋆ σ)
  --arr : ∀ {s : S l} → Num τ → Num (ix s ⇒ τ)
```
The set of numeric types and applications which return numeric types
```
data FNum : Ty → Set where
  num : Num τ → FNum τ
  fun : Num τ → FNum σ → FNum (τ ⇒ σ)
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
data Arit (ctxt : Ty → Set) : Ty → Set where
  var   : ctxt τ → Arit ctxt τ
  lam   : (ctxt τ → Arit ctxt σ) → Arit ctxt (τ ⇒ σ)
  app   : Arit ctxt (τ ⇒ σ) → Arit ctxt τ → Arit ctxt σ

  sizeN : Arit ctxt (ix s) → Arit ctxt N
  posiN : Arit ctxt (ix s) → Reshape p s → Arit ctxt N
  spliₗ : Arit ctxt (ix (s ⊗ p)) → Arit ctxt (ix s)
  spliᵣ : Arit ctxt (ix (s ⊗ p)) → Arit ctxt (ix p)

  _*N_ : Arit ctxt N → Arit ctxt N → Arit ctxt N 

  _*C_ : Arit ctxt C → Arit ctxt C → Arit ctxt C 
  ω`   : Arit ctxt N → Arit ctxt N → Arit ctxt C

  toC  : Arit ctxt R → Arit ctxt R → Arit ctxt C
  toRᵣ : Arit ctxt C → Arit ctxt R
  toRᵢ : Arit ctxt C → Arit ctxt R

  to-⋆     : Arit ctxt τ → Arit ctxt σ → Arit ctxt (τ ⋆ σ)
  ⋆-proj₁ : Arit ctxt (τ ⋆ σ) → Arit ctxt τ
  ⋆-proj₂ : Arit ctxt (τ ⋆ σ) → Arit ctxt σ
  
  _*R_ : Arit ctxt R → Arit ctxt R → Arit ctxt R 
  _+R_ : Arit ctxt R → Arit ctxt R → Arit ctxt R 
  _-R_ : Arit ctxt R → Arit ctxt R → Arit ctxt R 

  repeat       : (n : ℕ) → Arit ctxt τ → Arit ctxt (τ ◎ n)

  SIMD-*R      : {n : ℕ} → Arit ctxt (R ◎ n) → Arit ctxt (R ◎ n) → Arit ctxt (R ◎ n)
  SIMD-+R      : {n : ℕ} → Arit ctxt (R ◎ n) → Arit ctxt (R ◎ n) → Arit ctxt (R ◎ n)
  SIMD--R      : {n : ℕ} → Arit ctxt (R ◎ n) → Arit ctxt (R ◎ n) → Arit ctxt (R ◎ n)

  SIMD-to-⋆    : {n : ℕ} → Arit ctxt (τ ◎ n) → Arit ctxt (σ ◎ n) → Arit ctxt (τ ⋆ σ ◎ n)
  SIMD-⋆-proj₁ : {n : ℕ} → Arit ctxt (τ ⋆ σ ◎ n)  → Arit ctxt (τ ◎ n)
  SIMD-⋆-proj₂ : {n : ℕ} → Arit ctxt (τ ⋆ σ ◎ n)  → Arit ctxt (σ ◎ n)

  ωr`  : Arit ctxt N → Arit ctxt N → Arit ctxt R
  ωi`  : Arit ctxt N → Arit ctxt N → Arit ctxt R
```

```agda  

mult : {ctxt : Ty → Set} (a b c d : Arit ctxt R) → Arit ctxt (R ⋆ R)
mult a b c d = to-⋆ ((a *R c) -R (b *R d)) ((a *R d) +R (b *R c)) 

SIMD-mult : {n : ℕ} {ctxt : Ty → Set} (a b c d : Arit ctxt (R ◎ n)) → Arit ctxt (R ⋆ R ◎ n)
SIMD-mult a b c d = SIMD-to-⋆ (SIMD--R (SIMD-*R a c) (SIMD-*R b d)) (SIMD-+R (SIMD-*R a d) (SIMD-*R b c))

curry : ∀ {ctxt : Ty → Set} → ∀ { X : Set } → (Arit ctxt (R ⋆ R) → X) → (Arit ctxt R → Arit ctxt R → X)
curry f r i = f (to-⋆ r i)

SIMD-curry : ∀ {n : ℕ} {ctxt : Ty → Set} → ∀ { X : Set } → (Arit ctxt (R ⋆ R ◎ n) → X) → (Arit ctxt (R ◎ n) → Arit ctxt (R ◎ n) → X)
SIMD-curry f r i = f (SIMD-to-⋆ r i)

uncurry : ∀ {ctxt : Ty → Set} → ∀ { X : Set } → (Arit ctxt R → Arit ctxt R → X) → (Arit ctxt (R ⋆ R) → X)
uncurry f x = f (⋆-proj₁ x) (⋆-proj₂ x)

SIMD-uncurry : ∀ {n : ℕ} {ctxt : Ty → Set} → ∀ { X : Set } → (Arit ctxt (R ◎ n) → Arit ctxt (R ◎ n) → X) → (Arit ctxt (R ⋆ R ◎ n) → X)
SIMD-uncurry f x = f (SIMD-⋆-proj₁ x) (SIMD-⋆-proj₂ x)

{-
ω` : ∀ {ctxt : Ty → Set} → Arit ctxt N → Arit ctxt N → Arit ctxt C
ω` n j = toC (ωr` n j) (ωi` n j)
-}
{-
_*C_ : ∀ {ctxt} → Arit ctxt C → Arit ctxt C → Arit ctxt C 
x *C′ y =
  let a = toRᵣ x in
  let b = toRᵢ x in
  let c = toRᵣ y in
  let d = toRᵢ y in
  toC ((a *R c) -R (b *R d)) ((a *R d) +R (b *R c))
-}

--let′_=′_in′_ : ∀ {ctxt} → (ctxt τ) → (Arit ctxt τ) → Arit ctxt σ → Arit ctxt σ
--let′_=′_in′_ nm x y = app ? ?


infix 1 lam
syntax lam (λ x → e) = `λ x ⇒ e
```

Here I check that I have setup the lambda calculi correctly by ensuring I can 
represent the SKI operators
```agda
module _ where
  private variable
    ctxt : Ty → Set

  I` : Arit ctxt (τ ⇒ τ)
  I` = lam (λ x → var x)

  K` : Arit ctxt (τ ⇒ σ ⇒ τ)
  K` = lam λ x → lam λ y → var x
  -- 
  S` : Arit ctxt ((σ ⇒ δ ⇒ τ) ⇒ (σ ⇒ δ) ⇒ σ ⇒ τ)
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
lanes as opposed to a multiple of.

```agda
  --data IsSimd′ : {ℓ : L} (s : S ℓ) → Set where
  --  base : ∀ {n : ℕ} → IsSimd′ (ν (n *ₙ lane))

  {-
  data IsSimd : {ℓ : L} (s : S ℓ) → Set where
    base : ∀ {s : S zz} → IsSimd ((ι s) ⊗ ι lanes)
    down : ∀ {ℓ : L} {s : S ℓ} → IsSimd s → IsSimd (ι s)
    comp : ∀ {ℓ : L} {s p : S (ss ℓ)} → IsSimd s → IsSimd p → IsSimd (s ⊗ p)
  -}

  data Inp (ctxt : Ty → Set) : {l : L} (s : S l) {τ : Ty} (num : Num τ) → Set₁ where
    compose  : ∀ {s₁ : S l} {τ : Ty} {num : Num τ}
             → Inp ctxt s₁ num
             → Inp ctxt s₁ num
             → Inp ctxt s₁ num
    copyOut` : {s : S (ss l)} 
             → {p : S (ss l)}
             → {τ : Ty} {num : Num τ}
             → (r₁ : Reshape s p) 
             → (r₂ : Reshape p s) 
             → Inp ctxt p num
             → Inp ctxt (ι s) num
    part`    : ∀ {s p : S (ss l)} 
             → {τ : Ty} {num : Num τ}
             → (s⊂p : s ⊂ p) 
             → Inp ctxt (inv-⊂ s⊂p) num
             → Inp ctxt p num
    imap`    : ∀ {τ : Ty} {num : Num τ} 
             → Arit ctxt (ix s ⇒ τ ⇒ τ) → Inp ctxt s num
    mapSum`  : ∀ {u : ℕ} 
             → ∀ {τ : Ty} {num : Num τ}
             → Arit ctxt ((ar (ι (ν u)) τ) ⇒ ix (ι (ν u)) ⇒ ix (ι (ν u)) ⇒ τ) 
             → Inp ctxt (ι (ν u)) num
```
I need some way to pack from (s ⊗ ι (ν LANES)) τ into s (τ ◎ LANES)
Because this deals with Shape, I belive that this has to be an Inp operation
```agda
    packₗ : ∀ {τ} {n LANES : ℕ}
         → {num : Num τ}
         → {s : S (ss zz)}
         → Inp ctxt s (num ◎ LANES)
         → Inp ctxt (ι (ν (n * LANES)) ⊗ s) num
         
    packᵣ : ∀ {τ} {n LANES : ℕ}
         → {num : Num τ}
         → {s : S (ss zz)}
         → Inp ctxt s (num ◎ LANES)
         → Inp ctxt (s ⊗ ι (ν (n * LANES))) num
    

    -- What if, instead of working with pack as above, we create a bastardisation of part which will use simd at the next step...
    SIMDpart` : ∀ {s p : S (ss zz)}
              → {τ : Ty} {num : Num τ}
              → {n LANES : ℕ}
              → (s⊂p : (s ⊗ (ι (ν (n * LANES)))) ⊂ p)
              → Inp ctxt s (num ◎ LANES)
              → Inp ctxt p num
  {-
    packₗ : ∀ {τ} {n m LANES : ℕ}
         → {num : Num τ}
         → Inp ctxt ((ι (ν m))) (num ◎ LANES)
         → Inp ctxt (ι (ν (n * LANES)) ⊗ ι (ν m)) num
         
    packᵣ : ∀ {τ} {n m LANES : ℕ}
         → {num : Num τ}
         → Inp ctxt ((ι (ν m))) (num ◎ LANES)
         → Inp ctxt (ι (ν m) ⊗ ι (ν (n * LANES))) num
    -}
    {-
    pack : ∀ {τ : Ty} {m n LANES : ℕ}
         → {num : Num τ}
         → Inp ctxt (ι (ν n)) (num ◎ LANES)
         → Inp ctxt (ι (ν (m * LANES)) ⊗ ι (ν n)) num
    -}
    {-
    pack : ∀ {τ : Ty} {m n LANES : ℕ}
         → {num : Num τ}
         → Inp ctxt (ι (ν n)) (num ◎ LANES)
         → Inp ctxt (ι (ν n) ⊗ ι (ν (m * LANES))) num
    -}

    --pack : ∀ {τ : Ty} {n : ℕ}
    --pack : ∀ {τ : Ty} {n : ℕ}
    --      → {num : Num τ}
    --      → (v⊂s : (ι (ν n) ⊂ s))
    --      → Inp ctxt (inv-⊂ v⊂s) (num ◎ n)
    --      → Inp ctxt s num

    --packAny : ∀ {τ : Ty} {n : ℕ}
    --        → {num : Num τ}
    --        → ?
    {-
    simdSum : ∀ {u : ℕ}
            → ∀ {τ : Ty} {num : Num τ}
            → Arit ctxt ((ar (ι (ν u)) τ) ⇒ ix (ι (ν u)) ⇒ ix (ι (ν u)) ⇒ τ) 
            → Inp ctxt ((ι lanes) ⊗ (ι (ν u))) num
    simdImap` : ∀ {τ : Ty} {num : Num τ} 
              → {s : S (ss zz)}
              → Arit ctxt (ix s ⇒ τ ⇒ τ) 
              → Inp ctxt (ι lanes ⊗ s) num
    -}
  
  _>>>_ : ∀ {ctxt : Ty → Set} 
        → ∀ {l : L}
        → ∀ {s : S l}
        → ∀ {τ : Ty} {num : Num τ} 
        → Inp ctxt s num → Inp ctxt s num → Inp ctxt s num
  _>>>_ {ctxt} {_} {s} e₁ e₂ = compose e₁ e₂
```

Within these in place operations, we can then represent twiddles...


```agda
twid` : {s s′ p p′ : S (ss l)} {ctxt : Ty → Set} → (r₁ : Reshape s′ s) → (r₂ : Reshape p′ p) → Inp ctxt (s ⊗ p) (Scl C)
twid` {l} {s} {s′} {p} {p′} r₁ r₂ = 
      imap`
        (`λ i ⇒ `λ x ⇒ 
          (var x) *C
          ω` 
            (sizeN $ var i) 
            ((posiN (spliₗ $ var $ i) r₁) *N (posiN (spliᵣ $ var $ i) r₂))
        )

Rtwid` : {s s′ p p′ : S (ss l)} {ctxt : Ty → Set} → (r₁ : Reshape s′ s) → (r₂ : Reshape p′ p) → Inp ctxt (s ⊗ p) ((Scl R) ⋆ (Scl R))
Rtwid` {l} {s} {s′} {p} {p′} r₁ r₂ = 
      imap`
        (`λ i ⇒ `λ x ⇒ 
            let ωᵣ = ωr` (sizeN $ var i) ((posiN (spliₗ $ var $ i) r₁) *N (posiN (spliᵣ $ var $ i) r₂)) in
            let ωᵢ = ωi` (sizeN $ var i) ((posiN (spliₗ $ var $ i) r₁) *N (posiN (spliᵣ $ var $ i) r₂)) in
          (uncurry mult (var x)) ωᵣ ωᵢ
        )
```

```agda
--ndft` : ∀ {n : ℕ} → Inp (ar (ι (ν n)) C) (ar (ι (ν n)) C)
dft` : ∀ {s : S zz} {ctxt : Ty → Set} → Inp ctxt (ι s) (Scl C)
dft` {ν u} = mapSum` {u = u} $ `λ xs ⇒ `λ j ⇒ `λ k ⇒ (app (var xs) (var k)) *C (ω` (sizeN (var j)) ((posiN (var k) eq) *N (posiN (var j) eq)))

Rdft` : ∀ {s : S zz} {ctxt : Ty → Set} → Inp ctxt (ι s) ((Scl R) ⋆ (Scl R))
Rdft` {ν u} = mapSum` {u = u} $ `λ xs ⇒ `λ j ⇒ `λ k ⇒ 
    let ωᵣ  = ωr` (sizeN (var j)) ((posiN (var k) eq) *N (posiN (var j) eq)) in
    let ωᵢ  = ωi` (sizeN (var j)) ((posiN (var k) eq) *N (posiN (var j) eq)) in
    (uncurry mult (app (var xs) (var k))) ωᵣ ωᵢ

-- Should do N dft's in parallel
SIMDdft` : ∀ {s : S zz} {ctxt : Ty → Set} → {n : ℕ} → Inp ctxt (ι s) (((Scl R) ⋆ (Scl R)) ◎ n)
SIMDdft` {ν u} {ctxt} = mapSum` {u = u} $ `λ xs ⇒ `λ j ⇒ `λ k ⇒
    let ωᵣ  = ωr` (sizeN (var j)) ((posiN (var k) eq) *N (posiN (var j) eq)) in
    let ωᵢ  = ωi` (sizeN (var j)) ((posiN (var k) eq) *N (posiN (var j) eq)) in
    (SIMD-uncurry SIMD-mult (app (var xs) (var k))) (repeat _ ωᵣ) (repeat _ ωᵢ)
    
{-
SIMDdft`′ : ∀ {s : S zz} {ctxt : Ty → Set} → {n : ℕ} → Inp ctxt (ι (ν n) ⊗ (ι s)) ((Scl R) ⋆ (Scl R))
SIMDdft`′ {s} {ctxt} {n} = ?

-}
--module _ where
--  lanes : S zz
--  lanes = ν 3
  
  --SIMD* : {ctxt : Ty → Set} → Arit ctxt (SR′ ⇒ SR′ ⇒ SR′)
  --SIMD* {ctxt} = `λ a ⇒ `λ b ⇒ to-⋆ (((⋆-proj₁ (var a))) *R ((⋆-proj₁ (var b)))) (to-⋆ ? (to-⋆ ? ?))

  --simdDft` : {s : S zz} {ctxt : Ty → Set} → Inp ctxt (ι s) ((Scl R ⋆ Scl R ⋆ Scl R ⋆ Scl R) ⋆ (Scl R ⋆ Scl R ⋆ Scl R ⋆ Scl R))
  --simdDft` {ν x} = mapSum` ?
  --simdDft` : ∀ {s : S zz} {ctxt : Ty → Set} → Inp ctxt ((ι lanes) ⊗ (ι s)) (Scl C)
  --simdDft` {ν u} = simdSum {u = u} $ `λ xs ⇒ `λ j ⇒ `λ k ⇒ (app (var xs) (var k)) *C (ω` (sizeN (var j)) ((posiN (var k) eq) *N (posiN (var j) eq)))
```

# Defining the FFT

The return value of the standard implementation of the FFT over will return the 
input shape transposed because the last stage of the recursive step swaps the input.
Swaps are expensive and so we instead use the UFFT which push's all swaps to 
either the end or the start of the computation. If the input is given transposed,
I call it `pre-ufft`, if the output needs to be transposed, I call it `post-ufft`.
Both are defined here

```agda
pre-ufft`  : ∀ {ctxt : Ty → Set} → ∀ (lower-ft : ∀ {p : S l} → Inp ctxt (ι p) (Scl C))
          → ∀ {s : S (ss l)} → Inp ctxt s (Scl C)
pre-ufft` lower-ft {ι s} = lower-ft
pre-ufft` lower-ft {s ⊗ p} = part` (le sid) (pre-ufft` lower-ft {p})       -- Left ufft
                             >>> twid` {_} {s} {transp s} {p} {p} transpᵣ eq  -- Twiddles 
                             >>> part` (ri sid) (pre-ufft` lower-ft {s})       -- Right ufft

Rpre-ufft`  : ∀ {ctxt : Ty → Set} → ∀ (lower-ft : ∀ {p : S l} → Inp ctxt (ι p) ((Scl R) ⋆ (Scl R)))
          → ∀ {s : S (ss l)} → Inp ctxt s ((Scl R) ⋆ (Scl R))
Rpre-ufft` lower-ft {ι s} = lower-ft
Rpre-ufft` lower-ft {s ⊗ p} = part` (le sid) (Rpre-ufft` lower-ft {p})       -- Left ufft
                             >>> Rtwid` {_} {s} {transp s} {p} {p} transpᵣ eq  -- Twiddles 
                             >>> part` (ri sid) (Rpre-ufft` lower-ft {s})       -- Right ufft

--SIMD-Rpre-ufft : ∀ {ctxt : Ty → Set} {p : S (ss zz)} → Inp ctxt (transp p) (Scl R ⋆ Scl R)
```
The output of the following `post-ufft` would need to be transposed then 
change majored to be correct.
```agda
post-ufft` : ∀ {ctxt : Ty → Set} → ∀ (lower-ft : ∀ {p : S l} → Inp ctxt (ι p) (Scl C))
          → ∀ {s : S (ss l)} → Inp ctxt s (Scl C)
post-ufft` lower-ft {ι s} = lower-ft 
post-ufft` lower-ft {s ⊗ p} = part` (ri sid) (post-ufft` lower-ft {s})     -- Right ufft
                              >>> twid` {_} {s} {s} {p} {transp p} eq transpᵣ -- Twiddles 
                              >>> part` (le sid) (post-ufft` lower-ft {p})     -- Left ufft

Rpost-ufft` : ∀ {ctxt : Ty → Set} → ∀ (lower-ft : ∀ {p : S l} → Inp ctxt (ι p) ((Scl R) ⋆ (Scl R)))
          → ∀ {s : S (ss l)} → Inp ctxt s ((Scl R) ⋆ (Scl R))
Rpost-ufft` lower-ft {ι s} = lower-ft 
Rpost-ufft` lower-ft {s ⊗ p} = part` (ri sid) (Rpost-ufft` lower-ft {s})     -- Right ufft
                              >>> Rtwid` {_} {s} {s} {p} {transp p} eq transpᵣ -- Twiddles 
                              >>> part` (le sid) (Rpost-ufft` lower-ft {p})     -- Left ufft
```


We can then define `fftn` in our DSL.

```agda
fftn` : ∀ {ctxt : Ty → Set} → (s : S (ss (ss zz))) → Inp ctxt (ι s) (Scl C)
fftn` s = copyOut` eq (CMᵗ ∙ rev transpᵣ) (post-ufft` (copyOut` (rev transpᵣ) CMᵗ (pre-ufft` dft`))) 

Rfftn` : ∀ {ctxt : Ty → Set} → (s : S (ss (ss zz))) → Inp ctxt (ι s) ((Scl R) ⋆ (Scl R))
Rfftn` s = copyOut` eq (CMᵗ ∙ rev transpᵣ) (Rpost-ufft` (copyOut` (rev transpᵣ) CMᵗ (Rpre-ufft` Rdft`))) 

```
I've had to take some time to consider when a given shape is SIMD able, and 
have realised that we can easily represent this with the levels.
- Level zz    - remains as natural
- Level ss zz - Pose a restriction that (ι (ν n) ⊗ (ι (ν 4))) is the only valid 
                shape, this allows us to easily split when we want to use SIMD op's
              

```agda
module _ where

  LANES : ℕ
  LANES = 4
  
  {-
  data SIMD-able : ∀ {ℓ : L} → S ℓ → Set where
    base : (n : ℕ) → SIMD-able (ι (ι (ν n) ⊗ (ι (ν LANES))))
    _⊗_ : ∀ {ℓ : L} {s p : S (ss (ss ℓ))} → SIMD-able s → SIMD-able p → SIMD-able (s ⊗ p)
    ι : ∀ {ℓ : L} {s : S (ss ℓ)} → SIMD-able s → SIMD-able (ι s)
  -}

  data SIMD-able : ∀ {ℓ : L} → S ℓ → Set where
    base : (n : ℕ) → SIMD-able (ν (n * LANES))
    _⊗_ : ∀ {ℓ : L} {s p : S (ss ℓ)} → SIMD-able s → SIMD-able p → SIMD-able (s ⊗ p)
    ι : ∀ {ℓ : L} {s : S ℓ} → SIMD-able s → SIMD-able (ι s)

  -- For any SIMD-able shape, we can pull 

```
I could give something similar to SIMD, which lets you, for a shape of any level, 
pull the LANES from (ν (a * LANES)), as to "guide" the recursion
- But is this what I need????
  

```agda

{-
Rpost-ufft` : ∀ {ctxt : Ty → Set} → ∀ (lower-ft : ∀ {p : S l} → Inp ctxt (ι p) ((Scl R) ⋆ (Scl R)))
          → ∀ {s : S (ss l)} → Inp ctxt s ((Scl R) ⋆ (Scl R))
Rpost-ufft` lower-ft {ι s} = lower-ft 
Rpost-ufft` lower-ft {s ⊗ p} = part` (ri sid) (Rpost-ufft` lower-ft {s})     -- Right ufft
                              >>> Rtwid` {_} {s} {s} {p} {transp p} eq transpᵣ -- Twiddles 
                              >>> part` (le sid) (Rpost-ufft` lower-ft {p})     -- Left ufft
                              -}

  open import Data.Product
  -- Using this means I don't need to deal with Maybe 
  pull-left′ : {s₁ s₂ : S (ss zz)} → SIMD-able (s₁ ⊗ s₂) → ∃ λ n → (ι (ν (n * LANES))) ⊂ (s₁ ⊗ s₂)
  pull-left′ (ι (base n) ⊗ _) = n , le sid
  pull-left′ (SIMD@(_ ⊗ _) ⊗ _) = let n , sub = pull-left′ SIMD in n , (le (st sub))

  pull-coleft′ : {s₁ s₂ : S (ss zz)} → (SIMD : SIMD-able (s₁ ⊗ s₂)) → (inv-⊂ (pull-left′ SIMD .proj₂)) ⊂ (s₁ ⊗ s₂)
  pull-coleft′ (ι (base n) ⊗ SIMD₂) = ri sid
  pull-coleft′ ((SIMD₁ ⊗ SIMD₃) ⊗ SIMD₂) = bₗ (pull-coleft′ (SIMD₁ ⊗ SIMD₃)) sid

  pull-coleft : {s₁ s₂ : S (ss zz)} → (SIMD : SIMD-able (s₁ ⊗ s₂)) → ∃ λ s → s ⊂ (s₁ ⊗ s₂)
  pull-coleft {ι .(ν (n * LANES))} {s₂} (ι (base n) ⊗ SIMD₂) = s₂ , ri sid
  pull-coleft {s₁ ⊗ s₂} {s₃} ((SIMD₁ ⊗ SIMD₂) ⊗ SIMD₃) = let s , sub = pull-coleft (SIMD₁ ⊗ SIMD₂) in s ⊗ s₃ , bₗ sub sid

  pull-coleft-inv-is-base : ∀ {s₁ s₂ : S (ss zz)} → (SIMD : SIMD-able (s₁ ⊗ s₂)) → ∃ λ n → inv-⊂ (pull-coleft SIMD .proj₂) ≡ ι (ν (n * 4))
  pull-coleft-inv-is-base (ι (base n) ⊗ _) = n , refl
  pull-coleft-inv-is-base ((SIMD₁ ⊗ SIMD₂) ⊗ _) = pull-coleft-inv-is-base (SIMD₁ ⊗ SIMD₂)

  {-
  obi1 : ∀ {b} {c} {n} {x : SIMD-able b} {x₁ : SIMD-able c} →
       (ι (ν (n * LANES)) ⊗
        ι (ν (pull-coleft-inv-is-base (x ⊗ x₁) .proj₁ * LANES)))
       ≡ inv-⊂ (ri {_} {_} {ι (ν n)} (st (pull-coleft (x ⊗ x₁) .proj₂)))
  obi1 {b} {c} {n} {x} {x₁} = ?
  -}
  pull-left : (s : S (ss zz)) → SIMD-able s → ∃ λ n → (ι (ν (n * LANES))) ⊆ s
  pull-left (ι s) (ι (base n)) = n , sid
  pull-left (s ⊗ s₁) (SIMD ⊗ SIMD₁) = let n , sub = pull-left s SIMD in n , (st (le sub))

  pull-right′ : {s₁ s₂ : S (ss zz)} → SIMD-able (s₁ ⊗ s₂) → ∃ λ n → (ι (ν (n * LANES))) ⊂ (s₁ ⊗ s₂)
  pull-right′ (_ ⊗ ι (base n)) = n , ri sid
  pull-right′ (_ ⊗ SIMD@(_ ⊗ _)) = let n , sub = pull-right′ SIMD in n , (ri (st sub))
  
  SIMD-Rpost-ufft` : ∀ {ctxt : Ty → Set} → ∀ (lower-ft : ∀ {p : S zz} → Inp ctxt (ι p) (((Scl R) ⋆ (Scl R)) ◎ LANES))
            → ∀ {s : S ((ss zz))} → SIMD-able s → Inp ctxt s ((Scl R) ⋆ (Scl R))
  SIMD-Rpost-ufft` {ctxt} lower-ft {ι s} (ι SIMD) = ? -- Here we don't actually have a lower-ft we can use...
  SIMD-Rpost-ufft` {ctxt} lower-ft (ι (base n) ⊗ ι (base m)) =  
          packᵣ {n = m} lower-ft
      >>> Rtwid` eq transpᵣ
      >>> packₗ {n = n} lower-ft
  SIMD-Rpost-ufft` {ctxt} lower-ft {ι (ν .(n * LANES)) ⊗ (s₂ ⊗ s₃)} (ι (base n) ⊗ (SIMD₂ ⊗ SIMD₃)) = 
          SIMDpart` {ctxt} {_} {_} {_} {_} {pull-left′ (SIMD₂ ⊗ SIMD₃) .proj₁} (bᵣ sid (pull-left′ (SIMD₂ ⊗ SIMD₃) .proj₂)) lower-ft
      >>> Rtwid` eq transpᵣ
      >>> part` (le sid) (SIMD-Rpost-ufft` lower-ft (SIMD₂ ⊗ SIMD₃))
  SIMD-Rpost-ufft` {ctxt} lower-ft {(s₁ ⊗ s₂) ⊗ ι (ν .(n * LANES))} ((SIMD₁ ⊗ SIMD₂) ⊗ ι (base n)) = ?
  SIMD-Rpost-ufft` {ctxt} lower-ft {(s₁ ⊗ s₂) ⊗ (s₃ ⊗ s₄)} ((SIMD₁ ⊗ SIMD₂) ⊗ (SIMD₃ ⊗ SIMD₄)) = ?
  {-
  -- This is the case we can't do any SIMD, annoying by my own definition of lower-ft I also cant use that, maybe I need to take a non SIMD lower-ft and vectorise it automatically...
  SIMD-Rpost-ufft` lower-ft (ι (base n)) = ?
  -- These are the cases we can use simd 
  -- This first one is trivial, as we can easily see where we can bunch for SIMD
  SIMD-Rpost-ufft` lower-ft (ι (base n) ⊗ ι (base m)) = packᵣ {n = m} lower-ft
                                                      >>> Rtwid` eq transpᵣ
                                                      >>> packₗ {n = n} lower-ft
  SIMD-Rpost-ufft` {ctxt} lower-ft {(ι (ν (_))) ⊗ (b ⊗ c)} (SIMD-s@(ι (base n)) ⊗ SIMD-p@(_ ⊗ _)) = --rewrite pull-coleft-inv-is-base SIMD-p .proj₂ = 
                                                              --part` (ri (let a = pull-coleft′ SIMD-p in st a)) (packₗ ?)
                                                              --part` (bᵣ sid (pull-coleft′ SIMD-p)) ? --(SIMD-Rpost-ufft` lower-ft SIMD-s)
                                                              -- I want to use part so I get (ι (ν base )) ⊗ (ι (ν base))
                                                              
                                                                -- Here I know that inv-⊂ (pull-coleft (x ⊗ x₁)) is ι (ν m * 4)...
                                                                -- Proven in pull-coleft-inv-is-base
--
                                                            --- Subst here makes this absolutly grim
                                                              part` 
                                                                (ri (st (pull-coleft SIMD-p .proj₂))) 
                                                                (subst 
                                                                  (λ s → Inp ctxt s {R ⋆ R} ((Scl R) ⋆ (Scl R))) 
                                                                  (cong (_ ⊗_) (sym (pull-coleft-inv-is-base SIMD-p .proj₂))) 
                                                                  (packᵣ {n = pull-coleft-inv-is-base SIMD-p .proj₁} (lower-ft {ν (n * LANES)}))
                                                                ) --(packᵣ ?)
                                                          >>> Rtwid` eq transpᵣ
                                                          >>> part` (le sid) (SIMD-Rpost-ufft` lower-ft SIMD-p)

                                                          {-
                                                              part` (ri (st (pull-left′ _ _ SIMD-p .proj₂))) (packₗ ?) -- Ew - can't use lower-ft
                                                          >>> Rtwid` eq transpᵣ
                                                          >>> part` (le sid) (SIMD-Rpost-ufft` lower-ft SIMD-p)
                                                          -}
  SIMD-Rpost-ufft` lower-ft (SIMD-s@(_ ⊗ _) ⊗ ι (base n)) = part` (ri sid) (SIMD-Rpost-ufft` lower-ft SIMD-s)
                                                          >>> Rtwid` eq transpᵣ
                                                          >>> part` (le (?)) ?
  -- Then this is out recursive step, where we dont need to do anything for the DFT simd
  SIMD-Rpost-ufft` lower-ft (SIMD-s@(_ ⊗ _) ⊗ SIMD-p@(_ ⊗ _)) = part` (ri sid) (SIMD-Rpost-ufft` lower-ft SIMD-s)
                                                           >>> Rtwid` eq transpᵣ
                                                           >>> part` (le sid) (SIMD-Rpost-ufft` lower-ft SIMD-p)
  -}                                                          
  {-
  SIMD-map : ∀ {ctxt : Ty → Set} {n : ℕ} {s : S (ss zz)} {τ : Ty} {num : Num τ} → (f : Inp ctxt s (num ◎ LANES)) → Inp ctxt (ι ((ι s) ⊗ (ι (ι (ν n) ⊗ ι (ν LANES))))) num
  SIMD-map f = ? --part` (ri (st (le sid))) (pack (ri sid) f)

  SIMD-map′ : ∀ {ctxt : Ty → Set} {n : ℕ} {s : S (ss zz)} {τ : Ty} {num : Num τ} → (f : Inp ctxt s (num ◎ LANES)) → Inp ctxt (ι (ι (ι (ν n) ⊗ ι (ν LANES)) ⊗ (ι s))) num
  SIMD-map′ f = ? -- part` (le (st (le sid))) (pack (le sid) f)

  f : ∀ {ctxt : Ty → Set} → (∀ {p : S zz} → Inp ctxt (ι p) ((Scl R) ⋆ (Scl R))) → ∀ (s : S (ss (ss zz))) → (SIMD : SIMD-able (ι s)) → Inp ctxt (ι s) ((Scl R) ⋆ (Scl R))
  -- In this case we just have to do the DFT without SIMD
  f g (ι .(ι (ν n) ⊗ ι (ν LANES))) (ι (base n)) = ?
  -- Here are our three new main base cases where we are able to apply SIMD
  f g (ι .(ι (ν n) ⊗ ι (ν LANES)) ⊗ ι .(ι (ν m) ⊗ ι (ν LANES))) (ι (base n ⊗ base m)) =
    -- Effectively we want to loop over n, such that we have ι (ν LANES) ⊗ (ι (ν m * LANES)) 
    SIMD-map ?
    >>> ?
  f g (ι (.(ι (ν n)) ⊗ .(ι (ν LANES))) ⊗ (s₁ ⊗ s₂)) (ι (base n ⊗ simd₁)) = ?
  f g ((s ⊗ s₁) ⊗ ι (.(ι (ν n)) ⊗ .(ι (ν LANES)))) (ι (simd ⊗ base n)) = ?
  -- This is our new general recursive step, where we don't do squat about SIMD
  f g ((s ⊗ s₁) ⊗ (s₂ ⊗ s₃)) (ι (simd ⊗ simd₁)) = ?


  SIMD-Rfftn` : ∀ {ctxt : Ty → Set} → (s : S (ss (ss zz))) → Inp ctxt (ι s) ((Scl R) ⋆ (Scl R))
  SIMD-Rfftn` s = copyOut` eq (CMᵗ ∙ rev transpᵣ) (Rpost-ufft` (copyOut` (rev transpᵣ) CMᵗ ?)) 
  -}
```

One observation here is that we end up with `? >>> copy r₁ >>> copy r₂ >>> ?`
so I will need to make a small optimiser function which composes copy's (for 
when we want to use dropping a level to signify that we want to copy....... wait
a dang minute this isn't how I meant to do this)

# Big issues with the current status:

- Half the point of doing levels was that I wanted to use the change in levels 
to signify copying memory - this is currently completly ignored...
- Twiddles and the DFT are currently assumed to exit, it would be nice if these 
where defined from smaller components.
- Complex is currently represented as its own type, as opposed to pair of Reals.
- All the work I did towards SIMD hasn't been ported over.

I think the next big step is to change copy to something which has a 
distinction between changing levels and reshapes (i.e. only reshapes where the 
level doesn't change are allowed (this would need a pred and couldn't be done 
with `∀ {s s′ : S l} → Reshape s s′` as this could include `up eq ∙ down eq`)) 

For ℝ × ℝ ≡ ℂ, I need to think of a nice way to relate the dsl with the split 
to the Agda without.
