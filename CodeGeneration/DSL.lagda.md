
Here I define the DSL with which I can model the FFT. 
I should then be able to define a transpiler from an implementation in the DSL,
to Agda (to give semantics), and to `C` (to generate for performance).

```agda
module CodeGeneration.DSL where
open import Matrix.Mon
open import Matrix.NatMon

open import Matrix.Leveled.Base ℕ-Mon
open import Matrix.Leveled.Reshape ℕ-Mon
open import Matrix.Leveled.Change-Major ℕ-Mon
open import Matrix.Leveled.SubShape ℕ-Mon renaming (id to sid)
open import Matrix.Leveled.NatMon-Change-Major

open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality
open import Function.Base

_⊡_ = trans
```
TODO: I need to provide an implementation of CM-base for the naturals.
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
infixr 5 _⇒_
data Ty : Set where
  C : Ty
  N : Ty
  ix : {l : L} → S l → Ty
  _⇒_ : Ty → Ty → Ty

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
data Num : Ty → Set where
  C : Num C
  N : Num N
  arr : ∀ {s : S l} → Num τ → Num (ix s ⇒ τ)
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

  --NtoC  : Arit ctxt N      → Arit ctxt C
  sizeN : Arit ctxt (ix s) → Arit ctxt N
  posiN : Arit ctxt (ix s) → Reshape p s → Arit ctxt N
  spliₗ : Arit ctxt (ix (s ⊗ p)) → Arit ctxt (ix s)
  spliᵣ : Arit ctxt (ix (s ⊗ p)) → Arit ctxt (ix p)

  --_+N_ : Arit ctxt N → Arit ctxt N → Arit ctxt N 
  _*N_ : Arit ctxt N → Arit ctxt N → Arit ctxt N 
  --_+C_ : Arit ctxt C → Arit ctxt C → Arit ctxt C 
  _*C_ : Arit ctxt C → Arit ctxt C → Arit ctxt C 
  ω`   : Arit ctxt N → Arit ctxt N → Arit ctxt C

infix 1 lam
syntax lam (λ x → e) = `λ x ⇒ e
```
This is also nicer as I no longer need the here there notation.

Here I check that I have setup the lambda calculi correctly by ensuring I can 
represent the SKI operators
```agda
private variable
  ctxt : Ty → Set

I` : Arit ctxt (τ ⇒ τ)
I` = lam (λ x → var x)

K` : Arit ctxt (τ ⇒ σ ⇒ τ)
K` = lam λ x → lam λ y → var x
-- 
S` : Arit ctxt ((σ ⇒ δ ⇒ τ) ⇒ (σ ⇒ δ) ⇒ σ ⇒ τ)
S` = `λ x ⇒ `λ y ⇒ `λ z ⇒ app (app (var x) (var z)) (app (var y) (var z))

{-
_ : ∀ {τ δ σ : Ty} → app {ctxt} (app (app S` K`) (S` {ctxt} {τ} {δ})) K` ≡ app (app K` K`) (app (S` {ctxt} {τ} {δ}) K`)
_ = ?

_ : ∀ {x y} → app {ctxt} {τ} (app (app (S` {_} {_} {σ}) K`) (var x)) (var y) ≡ (var y)
_ = ? 
-}
```

I make a quick stop here to define the set of Ty elements which can use the 
same memory location, to allow us to eventually daisy chain when we want to put
ι 8 in ι 2 ⊗ ι 4 memory

```agda
data memCompat : Ty → Ty → Set where
  eq : memCompat τ τ
  eqSize : ∀ {l l′ : L} {s : S l} {s′ : S l′} → length s ≡ length s′ → memCompat τ σ → memCompat (ar s τ) (ar s σ)

memCompatible : memCompat τ σ → τ ≡ σ
memCompatible eq = refl
memCompatible (eqSize x x₁) rewrite memCompatible x₁ = refl
```

# The set of in place operations

We can then define the set of In-Place operations `Inp`.

We restrict these to currently operate over one shape level `l`
```agda
infixl 2 _>>>_
open import Data.Default

data Inp (ctxt : Ty → Set) : {l : L} (s : S l) → (s′ : S l) → .(Reshape s s′) → Set₁ where
  compose : ∀ {s₁ s₂ s₃ : S l} → (r₁ : Reshape s₁ s₂) → Inp ctxt s₁ s₂ r₁ → (r₂ : Reshape s₂ s₃) → Inp ctxt s₂ s₃ r₂ →  Inp ctxt s₁ s₃ (r₂ ∙ r₁)
  -- Restricted
  view` : ∀ {s s′ : S l} → (r : Reshape s s′) → Inp ctxt s s eq → Inp ctxt s s′ r
  copyOut` : {s p q : S (ss l)} → (r₁ : Reshape s p) → (r₂ : Reshape q s) → Inp ctxt p q (rev r₂ ∙ rev r₁) → Inp ctxt (ι s) (ι s) eq
  part`    : ∀ {s p : S (ss l)} → (s⊂p : s ⊂ p) → Inp ctxt (inv-⊂ s⊂p) (inv-⊂ s⊂p) eq → Inp ctxt p p eq
  imap`    : Arit ctxt (ix s ⇒ C ⇒ C) → Inp ctxt s s eq
  mapSum`  : ∀ {u : ℕ} → Arit ctxt ((ar (ι (ν u)) C) ⇒ ix (ι (ν u)) ⇒ ix (ι (ν u)) ⇒ C) → Inp ctxt (ι (ν u)) (ι (ν u)) eq
  --nop      : ∀ {s : S l} → Inp ctxt s s eq
  
_>>>_ : ∀ {ctxt : Ty → Set} 
      → ∀ {l : L}
      → ∀ {s : S l}
      → Inp ctxt s s eq → Inp ctxt s s eq → Inp ctxt s s eq
_>>>_ {ctxt} {_} {s} e₁ e₂ = compose eq e₁ eq e₂
```

Within these in place operations, we can then represent twiddles...

```agda
twid` : {s s′ p p′ : S (ss l)} {ctxt : Ty → Set} → (r₁ : Reshape s′ s) → (r₂ : Reshape p′ p) → Inp ctxt (s ⊗ p) (s ⊗ p) eq
twid` {l} {s} {s′} {p} {p′} r₁ r₂ = 
      imap` 
        (`λ x ⇒ `λ y ⇒ 
          (var y) *C
          ω` 
            (sizeN $ var x) 
            ((posiN (spliₗ $ var $ x) r₁) *N (posiN (spliᵣ $ var $ x) r₂))
        )
```

```agda
--ndft` : ∀ {n : ℕ} → Inp (ar (ι (ν n)) C) (ar (ι (ν n)) C)
dft` : ∀ {s : S zz} {ctxt : Ty → Set} → Inp ctxt (ι s) (ι s) eq
dft` {ν u} = mapSum` {u = u} $ `λ xs ⇒ `λ j ⇒ `λ k ⇒ (app (var xs) (var k)) *C (ω` (sizeN (var j)) ((posiN (var k) eq) *N (posiN (var j) eq)))
```

# Defining the FFT

The return value of the standard implementation of the FFT over will return the 
input shape transposed because the last stage of the recursive step swaps the input.
Swaps are expensive and so we instead use the UFFT which push's all swaps to 
either the end or the start of the computation. If the input is given transposed,
I call it `pre-ufft`, if the output needs to be transposed, I call it `post-ufft`.
Both are defined here

```agda
pre-ufft`  : ∀ {ctxt : Ty → Set} → ∀ (lower-ft : ∀ {p : S l} → Inp ctxt (ι p) (ι p) eq)
          → ∀ {s : S (ss l)} → Inp ctxt s s eq
pre-ufft` lower-ft {ι s} = lower-ft
pre-ufft` {_} {ctxt} lower-ft {s ⊗ p} = part` (le sid) (pre-ufft` lower-ft {p})       -- Left ufft
                             >>> twid` {_} {s} {transp s} {p} {p} transpᵣ eq  -- Twiddles 
                             >>> part` (ri sid) (pre-ufft` lower-ft {s})       -- Right ufft

```
The output of the following `post-ufft` would need to be transposed then 
change majored to be correct.
```agda
post-ufft` : ∀ {ctxt : Ty → Set} → ∀ (lower-ft : ∀ {p : S l} → Inp ctxt (ι p) (ι p) eq)
          → ∀ {s : S (ss l)} → Inp ctxt s s eq
post-ufft` lower-ft {ι s} = lower-ft 
post-ufft` lower-ft {s ⊗ p} = part` (ri sid) (post-ufft` lower-ft {s})     -- Right ufft
                              >>> twid` {_} {s} {s} {p} {transp p} eq transpᵣ -- Twiddles 
                              >>> part` (le sid) (post-ufft` lower-ft {p})     -- Left ufft
```


We can then define `fftn` in our DSL.

```agda
fftn` : ∀ {ctxt : Ty → Set} → (s : S (ss (ss zz))) → Inp ctxt s s eq
fftn` s = 
     -- compose eq (post-ufft` (copyOut` (rev transpᵣ) CMᵗ (pre-ufft` dft`))) (CMᵗ ∙ rev transpᵣ) nop
     
     view` (CMᵗ ∙ rev transpᵣ) (post-ufft` (copyOut` (rev transpᵣ) CMᵗ (pre-ufft` dft`)))
{-
-}
```

And then see how that looks for some shapes (Contains holes so commented)
```agda
{-
_ : fftn` (ι ? ⊗ ι ?) ≡ ?
_ = ?
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
