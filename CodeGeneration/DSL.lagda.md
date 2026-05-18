
Here I define the DSL with which I can model the FFT. 
I should then be able to define a transpiler from an implementation in the DSL,
to Agda (to give semantics), and to `C` (to generate for performance).

```agda
module CodeGeneration.DSL where
open import Matrix.Mon
open import Matrix.NatMon

open import Matrix.Leveled ℕ-Mon
open import Matrix.Leveled.SubShape ℕ-Mon
open import Matrix.Leveled.NatMon-Change-Major

open import Data.Nat
open import Relation.Binary.PropositionalEquality
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

For now I will just deal with Complex as a type - this needs to be changed to ℝ × ℝ
but this is probably best left till later (have done it before and should be 
an easy conversion).
```agda
infixr 5 _⇒_
data Ty : Set where
  C : Ty
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

# The set of in place operations

We can then define the set of In-Place operations `Inp`.

```agda
infixl 2 _>>>_
data Inp : Ty → Ty → Set where
```
We first define composition between two in-place operations.
```agda
  _>>>_ : Inp τ δ → Inp δ σ → Inp τ σ
```
For now, we add `dft` to our language - it would be nice for this to eventually
be derivable, but this works for now. 
We use level `zz` to declare that the dft operates over a single dimensional array
```agda
  dft` : ∀ {s : S zz} → Inp (ar s C) (ar s C)
```
We then define copy, this allows us to use reshapes as we "copy" data.
```agda
  copy` : Reshape s p → Inp (ar s τ) (ar p τ)
```
Not sure how I want to do this - need some kind of replacement for s ⊂ p but 
recall that I idaeally don't want \_⊂\_ as it can just be reduced down to reshapes
```agda
  part`  : (s⊂p : s ⊂ p) → Inp (ar (inv-⊂ s⊂p) τ) (ar (inv-⊂ s⊂p) τ) → Inp (ar p τ) (ar p τ)
  --part`  : Inp (ar s τ) (ar s τ) → (s⊂p : s ⊂ p) → Inp (ar p τ) (ar p τ)
```
I then need to think about some way of representing the twiddles
for previous implementations I have defined the twiddles as part of the DSL,
this is more challenging now that I need to reshape the input to the twiddles...
```agda
  twid` : {s s′ p p′ : S (ss l)} → Reshape s′ s → Reshape p′ p → Inp (ar (s ⊗ p) C) (ar (s ⊗ p) C)
```


# Defining the FFT

The return value of the standard implementation of the FFT over will return the 
input shape transposed because the last stage of the recursive step swaps the input.
Swaps are expensive and so we instead use the UFFT which push's all swaps to 
either the end or the start of the computation. If the input is given transposed,
I call it `pre-ufft`, if the output needs to be transposed, I call it `post-ufft`.
Both are defined here

```agda
pre-ufft`  : ∀ (lower-ft : ∀ {p : S l} → Inp (ar p C) (ar p C))
          → ∀ {s : S (ss l)} → Inp (ar s C) (ar s C)
pre-ufft` {l} lower-ft {ι s} = copy` (down eq) >>> lower-ft >>> copy` (up eq)
pre-ufft` {l} lower-ft {s ⊗ p} = part` (le id) (pre-ufft` lower-ft {p})       -- Left ufft
                             >>> twid` {_} {s} {transp s} {p} {p} transpᵣ eq  -- Twiddles 
                             >>> part` (ri id) (pre-ufft` lower-ft {s})       -- Right ufft
```
The output of the following `post-ufft` would need to be transposed then 
change majored to be correct.
```agda
post-ufft` : ∀ (lower-ft : ∀ {p : S l} → Inp (ar p C) (ar p C))
          → ∀ {s : S (ss l)} → Inp (ar s C) (ar s C)
post-ufft` {l} lower-ft {ι s} = copy` (down eq) >>> lower-ft >>> copy` (up eq)
post-ufft` {l} lower-ft {s ⊗ p} = part` (ri id) (post-ufft` lower-ft {s})     -- Right ufft
                              >>> twid` {_} {s} {s} {p} {transp p} eq transpᵣ -- Twiddles 
                              >>> part` (le id) (post-ufft` lower-ft {p})     -- Left ufft
```


We can then define `fftn` in our DSL.

```agda
fftn` : (s : S (ss (ss zz))) → Inp (ar s C) (ar s C)
fftn` s = post-ufft` (copy` (rev transpᵣ) >>> pre-ufft` dft` >>> copy` CMᵗ) 
     >>> copy` (CMᵗ ∙ rev transpᵣ)
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
