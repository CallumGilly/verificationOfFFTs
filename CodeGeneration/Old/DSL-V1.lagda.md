
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

# The DSL
Given the basic typing system, I can now create the DSL.

Here I actually make use of two parts for the DSL:
- The first comprises the set of arithmetic operations.
- The second comprises the set of in place operations.

# The set of arithmetic operations
I initially created the following definitions for Airthmatic, this failed when I
started writing for transpilation as what does context become...
We first need to define the context of operations
```agda
module OLD where
  infixl 10 _▹_ 
  data Ctxt : Set where
    ε : Ctxt
    _▹_ : Ctxt → Ty → Ctxt
  private 
    variable
      ctxt : Ctxt

  data _∈_ (τ : Ty) : (ctxt : Ctxt) → Set where
    here : ∀ {ctxt : Ctxt} → τ ∈ (ctxt ▹ τ)
    there : ∀ {ctxt : Ctxt} {σ : Ty} → τ ∈ ctxt → τ ∈ (ctxt ▹ σ)

  data Arit : Ctxt → Ty → Set where
    var   : τ ∈ ctxt → Arit ctxt τ
    lam   : Arit (ctxt ▹ τ) σ → Arit ctxt (τ ⇒ σ)
    app   : Arit ctxt (τ ⇒ σ) → Arit ctxt τ → Arit ctxt σ

    NtoC  : Arit ctxt N      → Arit ctxt C
    sizeN : Arit ctxt (ix s) → Arit ctxt N
    posiN : Arit ctxt (ix s) → Reshape p s → Arit ctxt N
    spliₗ : Arit ctxt (ix (s ⊗ p)) → Arit ctxt (ix s)
    spliᵣ : Arit ctxt (ix (s ⊗ p)) → Arit ctxt (ix p)

    _+N_ : Arit ctxt N → Arit ctxt N → Arit ctxt N 
    _*N_ : Arit ctxt N → Arit ctxt N → Arit ctxt N 
    _+C_ : Arit ctxt C → Arit ctxt C → Arit ctxt C 
    _*C_ : Arit ctxt C → Arit ctxt C → Arit ctxt C 
    ω`   : Arit ctxt N → Arit ctxt N → Arit ctxt C
```
Luckily, although this method of dealing with contexts was wrong, that only effects 
the lambda calculi

```agda
data Arit` (ctxt : Ty → Set) : Ty → Set where
  var   : ctxt τ → Arit` ctxt τ
  lam   : (ctxt τ → Arit` ctxt σ) → Arit` ctxt (τ ⇒ σ)
  app   : Arit` ctxt (τ ⇒ σ) → Arit` ctxt τ → Arit` ctxt σ

  NtoC  : Arit` ctxt N      → Arit` ctxt C
  sizeN : Arit` ctxt (ix s) → Arit` ctxt N
  posiN : Arit` ctxt (ix s) → Reshape p s → Arit` ctxt N
  spliₗ : Arit` ctxt (ix (s ⊗ p)) → Arit` ctxt (ix s)
  spliᵣ : Arit` ctxt (ix (s ⊗ p)) → Arit` ctxt (ix p)

  _+N_ : Arit` ctxt N → Arit` ctxt N → Arit` ctxt N 
  _*N_ : Arit` ctxt N → Arit` ctxt N → Arit` ctxt N 
  _+C_ : Arit` ctxt C → Arit` ctxt C → Arit` ctxt C 
  _*C_ : Arit` ctxt C → Arit` ctxt C → Arit` ctxt C 
  ω`   : Arit` ctxt N → Arit` ctxt N → Arit` ctxt C

infix 1 lam
syntax lam (λ x → e) = `λ x ⇒ e
```
This is also nicer as I no longer need the here there notation.

And check that I have setup the lambda calculi correctly
```agda
private variable
  ctxt : Ty → Set

I` : Arit` ctxt (τ ⇒ τ)
I` = lam (λ x → var x)

K` : Arit` ctxt (τ ⇒ σ ⇒ τ)
K` = lam λ x → lam λ y → var x
-- 
S` : Arit` ctxt ((σ ⇒ δ ⇒ τ) ⇒ (σ ⇒ δ) ⇒ σ ⇒ τ)
S` = `λ x ⇒ `λ y ⇒ `λ z ⇒ app (app (var x) (var z)) (app (var y) (var z))

{-
_ : ∀ {x y} → app {ctxt} {τ} (app (app (S` {_} {_} {σ}) K`) (var x)) (var y) ≡ (var y)
_ = ?
-}
```
# The set of in place operations

We can then define the set of In-Place operations `Inp`.

```agda
infixl 2 _>>>_
data Inp : Ty → Ty → Set₁ where
```
We first define composition between two in-place operations.
```agda
  _>>>_ : Inp τ δ → Inp δ σ → Inp τ σ
```
We then define copy, this allows us to use reshapes as we "copy" data.
```agda
  view` : (r : Reshape s p) → Inp (ar s τ) (ar p τ)
  --copy` : ∀ {s : S l} → Inp (ar s τ) (ar s τ) → Inp (ar (ι s) τ) (ar (ι s) τ)
  copyOut` : ∀ {s p q : S l} → Reshape s p → Reshape q s → Inp (ar p τ) (ar q τ) → Inp (ar (ι s) τ) (ar (ι s) τ)
```
Not sure how I want to do this - need some kind of replacement for s ⊂ p but 
recall that I idaeally don't want \_⊂\_ as it can just be reduced down to reshapes
```agda
  part`    : ∀ {s p : S (ss l)} → (s⊂p : s ⊂ p) → Inp (ar (inv-⊂ s⊂p) τ) (ar (inv-⊂ s⊂p) τ) → Inp (ar p τ) (ar p τ)
  --part`  : Inp (ar s τ) (ar s τ) → (s⊂p : s ⊂ p) → Inp (ar p τ) (ar p τ)
```
To implement DFT and Twiddles, we then need to create imap and sum.
```agda
  imap`    : Arit` ctxt (ix s ⇒ C ⇒ C) → Inp (ar s C) (ar s C)
```
Map sum needs a bit of thinking, as for each index it needs to do an operation 
for each index again knowing both `mapSum` : Array -> IxToPutElem -> CurrentIndex` → ?
```agda
  mapSum`  : Arit` ctxt ((ar s τ) ⇒ ix s ⇒ ix s ⇒ τ) → Inp (ar s C) (ar s C)
```

In place of the above two (`dft` and `twid`), we could have some kind of 
"expression" language in which we can represent the dft, twid and more...
```agda
twid` : {s s′ p p′ : S (ss l)} {ctxt : Ty → Set} → Reshape s′ s → Reshape p′ p → Inp (ar (s ⊗ p) C) (ar (s ⊗ p) C)
twid` {l} {s} {s′} {p} {p′} {ctxt} r₁ r₂ = 
      imap` {ctxt = ctxt} 
        (`λ x ⇒ `λ y ⇒ 
          (var y) *C
          ω` 
            (sizeN $ var x) 
            ((posiN (spliₗ $ var $ x) r₁) *N (posiN (spliᵣ $ var $ x) r₂))
        )
```

```agda
--ndft` : ∀ {n : ℕ} → Inp (ar (ι (ν n)) C) (ar (ι (ν n)) C)
dft` : ∀ {s : S zz} {ctxt : Ty → Set} → Inp (ar (ι s) C) (ar (ι s) C)
dft` {s} {ctxt} = mapSum` {ctxt = ctxt} $ `λ xs ⇒ `λ j ⇒ `λ k ⇒ (app (var xs) (var k)) *C (ω` (sizeN (var j)) ((posiN (var k) eq) *N (posiN (var j) eq)))

{-
dft` = mapSum` {τ = C} $ lam $ lam $ lam $ (app (var $ there $ there $ here) (var here)) *C ω` (sizeN (var here)) ((posiN (var here) (rev u-flattenᵣ)) *N (posiN (var $ there $ here) (rev u-flattenᵣ)))
-}
```

If we want expressions to be an in place operation, there input and output 
should be of the same type, but we also want to be able to map expressions over data.
```agda
{-
  expr` : E ε (τ ⇒ τ) → Inp τ τ 
  exprCpy` : E ε (ar s τ ⇒ ix s ⇒ τ) → Inp (ar s τ) (ar s τ)

data E (ctxt : Ctxt) : Ty → Set
data E ctxt where
  ` : ? → E ctxt τ
  `lam : E (ctxt ▹ τ) σ → E ctxt (τ ⇒ σ)
  `$   : E ctxt (τ ⇒ σ) → E ctxt τ → E ctxt σ
  _`+_ : E ctxt C → E ctxt C → E ctxt C
  _`*_ : E ctxt C → E ctxt C → E ctxt C
  `resh  : ∀ {s s′ : S l} → E ctxt (ix s) → Reshape s′ s → E ctxt (ix s′)
  `index : E ctxt (ix s) → E ctxt N
  `size  : E ctxt (ix s) → E ctxt N
  `twiddle : E ctxt N → E ctxt (ix s) → E  ctxt (ix s)
  `itter : (s : S l) → E ctxt (ix s ⇒ τ) → E ctxt (τ)
  -}
```

# Minimum Operation
One of the smallest operations is the identity function:

```agda
--id` : ∀ {s : S l} → Inp (ar s τ) (ar s τ)
--id` {l} {τ} {s} = ? --exprCpy` ? (`lam λ a → `lam λ b → `$ {_} {?} {_} a b )
```


# Defining the FFT

The return value of the standard implementation of the FFT over will return the 
input shape transposed because the last stage of the recursive step swaps the input.
Swaps are expensive and so we instead use the UFFT which push's all swaps to 
either the end or the start of the computation. If the input is given transposed,
I call it `pre-ufft`, if the output needs to be transposed, I call it `post-ufft`.
Both are defined here

```agda
pre-ufft`  : ∀ {ctxt : Ty → Set} → ∀ (lower-ft : ∀ {p : S l} → Inp (ar (ι p) C) (ar (ι p) C))
          → ∀ {s : S (ss l)} → Inp (ar s C) (ar s C)
pre-ufft` lower-ft {ι s} = lower-ft
pre-ufft` {_} {ctxt} lower-ft {s ⊗ p} = part` (le sid) (pre-ufft` {ctxt = ctxt} lower-ft {p})       -- Left ufft
                             >>> twid` {_} {s} {transp s} {p} {p} {ctxt} transpᵣ eq  -- Twiddles 
                             >>> part` (ri sid) (pre-ufft` {ctxt = ctxt} lower-ft {s})       -- Right ufft
```
The output of the following `post-ufft` would need to be transposed then 
change majored to be correct.
```agda
post-ufft` : ∀ {ctxt : Ty → Set} → ∀ (lower-ft : ∀ {p : S l} → Inp (ar (ι p) C) (ar (ι p) C))
          → ∀ {s : S (ss l)} → Inp (ar s C) (ar s C)
post-ufft` lower-ft {ι s} = lower-ft 
post-ufft` {_} {ctxt} lower-ft {s ⊗ p} = part` (ri sid) (post-ufft` {ctxt = ctxt} lower-ft {s})     -- Right ufft
                              >>> twid` {_} {s} {s} {p} {transp p} {ctxt} eq transpᵣ -- Twiddles 
                              >>> part` (le sid) (post-ufft` {ctxt = ctxt} lower-ft {p})     -- Left ufft
```


We can then define `fftn` in our DSL.

```agda
fftn` : ∀ {ctxt : Ty → Set} → (s : S (ss (ss zz))) → Inp (ar s C) (ar s C)
fftn` {ctxt} s = post-ufft` {ctxt = ctxt} (copyOut` (rev transpᵣ) CMᵗ (pre-ufft` {ctxt = ctxt} (dft` {ctxt = ctxt}))) 
     >>> view` (CMᵗ ∙ rev transpᵣ)
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
