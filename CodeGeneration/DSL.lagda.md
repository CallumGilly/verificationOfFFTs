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

variable
  l : L
  s p : S l
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
module Contexts (Ty : Set) where
  private 
    variable
      τ σ : Ty

  infixr 7 _◃_ 

  data Ctxt : Set where
    ⊘ : Ctxt
    _◃_ : Ty → Ctxt → Ctxt

  variable
    Γ Δ Φ : Ctxt

  data _∋_ : Ctxt → Ty → Set where
    here  : (τ ◃ Γ) ∋ τ
    there : Γ ∋ τ → (σ ◃ Γ) ∋ τ

  {-
  -- Now defined by CtxtSem
  data All (P : Ty → Set) : Ctxt → Set where 
    ⊘   : All P ⊘
    _◂_ : P τ → All P Γ → All P (τ ◃ Γ)
  -}

  data NonEmpty : Ctxt → Set where
    ne : NonEmpty (τ ◃ Γ)

  mapCtxt : Ctxt → (Ty → Ty) → Ctxt
  mapCtxt ⊘ f = ⊘
  mapCtxt (a ◃ Γ) f = f a ◃ mapCtxt Γ f

  -- Order preserving
  data _⊆ᶜ_ : Ctxt → Ctxt → Set where
    empt : ⊘ ⊆ᶜ Γ
    drop : Δ ⊆ᶜ Γ →      Δ  ⊆ᶜ (τ ◃ Γ)
    here : Δ ⊆ᶜ Γ → (τ ◃ Δ) ⊆ᶜ (τ ◃ Γ)

  data _∶_⊆ₚ_ (P : Ty → Set) : Ctxt → Ctxt → Set where
    empt : P ∶ ⊘ ⊆ₚ Γ 
    drop : P ∶ Δ ⊆ₚ Γ →       P ∶      Δ  ⊆ₚ (τ ◃ Γ)
    here : P ∶ Δ ⊆ₚ Γ → P τ → P ∶ (τ ◃ Δ) ⊆ₚ (τ ◃ Γ)

  -- data each (P : Ty → Set) (P₂ : (τ : Ty) → P τ → Set) : _∶_⊆ₚ_ P Δ Γ → Set where
  --   empt : each ?




  -- This is actually very useful - not only does it allow me to define 
  -- Semantics for Ty, but I think it also defines All :)
  module CtxtSem (Sem : Ty → Set) where
    data CtxtVal : Ctxt → Set where
      ⊘ : CtxtVal ⊘
      _◃_ : Sem τ → CtxtVal Γ → CtxtVal (τ ◃ Γ)

    pull : CtxtVal Γ → Γ ∋ τ → Sem τ
    pull (x ◃ _) here = x
    pull (_ ◃ Γ) (there ni) = pull Γ ni

  module _ where
    private open CtxtSem hiding (pull)
    All : (Ty → Set) → Ctxt → Set
    All = CtxtVal

    private variable 
      P₁ : Ty → Set
      Γₚ : All P₁ Γ
      τₚ : P₁ τ
    
    -- All with two dependent properties
    {-
    data All₂ (P₁ : Ty → Set) (P₂ : (τ : Ty) → P₁ τ → Set) : (Γ : Ctxt) → Set where
      ⊘ : All₂ _ _ ⊘
      rec : (τₚ₂ : P₂ τ ?) → All₂ P₁ P₂ Γ → All₂ _ _ (τ ◃ Γ)
    -}

    --data All′ (P : ?) : (Γₚ : All′ ? ?) → Set where
    
    -- How do I generalise for $n$ many dependent properties??
    --data Allₙ : (Γ : Ctxt) → Set where

  -- For now, when an all is dependent on annother All, I will just use Σ, but 
  -- I strongly feel that there is a smart way of doing this
  {-
    -- I need a form of all which is dependent on the prior all
    -- P₁ : Ty → Set
    -- P₂ : (τ : Ty) → P₁ τ → Set
    -- All P₁ Γ
    -- All P₂ Γ
    -- All (Ε P₂)

    --AllP : (P₁ : Ty → Set) → (P₂ : (τ : Ty) → P₁ τ → Set) → All P₁ Δ → Set
    --AllP P₁ P₂ = ?

    data All₂ (P₁ : Ty → Set) (P₂ : (τ : Ty) → P₁ τ → Set) : (Γ : Ctxt) → All P₁ Γ → Set where
      ⊘ : All₂ P₁ P₂ ⊘ ⊘
      _◃_ : (τₚ : P₁ τ) → P₂ τ τₚ → All₂ P₁ P₂ Γ Γₚ → All₂ P₁ P₂ (τ ◃ Γ) (τₚ ◃ Γₚ)

  module _ (P₁ : Ty → Set) (P₂ : (τ : Ty) → P₁ τ → Set) where
    private open CtxtSem
    open import Data.Product
    AllP : All P₁ Δ → All (λ τ → Σ (P₁ τ) (P₂ τ)) Δ
    AllP ⊘ = ⊘
    AllP (τₚ ◃ Γₚ) = (τₚ , ?) ◃ AllP Γₚ
  -}

module Types where

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

  variable
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

  -- A context can contain arrays, and Scalars
  data ConTy : Ty → Set where
    CNum : Num τ → ConTy τ
    CIx : ConTy (ix s)
    CArr : ∀ {s : S l} → Num τ → ConTy (ix s ⇒ τ)

  data Arr : Ty → Set where
    ARR : ∀ {s : S l} → Num τ → Arr (ix s ⇒ τ)
    
  
  module _ where
    open import Data.Maybe renaming (zipWith to zipWithₘ; map to mapₘ)

    isScalar : (τ : Ty) → Maybe (Scalar τ)
    isScalar C = just C
    isScalar R = just R
    isScalar N = just N
    isScalar ℝ = just ℝ
    isScalar _ = nothing

    isNum : (τ : Ty) → Maybe (Num τ)
    isNum (_ ⇒ _) = nothing
    isNum (ix x)  = nothing
    isNum (τ ⋆ σ) = zipWithₘ _⋆_ (isNum τ) (isNum σ)
    isNum x = mapₘ Scl (isScalar x) 

    isConTy : (τ : Ty) → Maybe (ConTy τ)
    isConTy (ix _ ⇒ τ) = mapₘ CArr (isNum τ)
    --isConTy (_    ⇒ _) = nothing
    isConTy (ix x) = just CIx
    isConTy = mapₘ CNum ∘ isNum
```

```agda
open Types
open Contexts Ty

{-
Ctxt-to-Ty : (Γ : Ctxt) → NonEmpty Γ → Ty
Ctxt-to-Ty (τ ◃ Γ) ne = ?

allTys : Ctxt → Ty → Ty
allTys ⊘ σ = σ
allTys (_◃_ {τ} _ Γ) σ = τ ⇒ (allTys Γ σ)

-- This is pretty grim...
_ : ∀ {τ σ₁ σ₂ σ₃ : Ty} 
  → ∀ {x : ConTy σ₁}
  → ∀ {y : ConTy σ₂} 
  → ∀ {z : ConTy σ₃}
  → allTys (x ◃ y ◃ z ◃ ⊘) τ ≡ σ₁ ⇒ (σ₂ ⇒ (σ₃ ⇒ τ))
_ = refl
{-# WARNING_ON_USAGE allTys "TODO: Update to be more consistently named and have a form with non empty and maybe a form without" #-}

Ctxt-to-⋆ : (Γ : Ctxt) → NonEmpty Γ → Ty
Ctxt-to-⋆ (_◃_ {τ} _ ⊘        ) ne = τ
Ctxt-to-⋆ (_◃_ {τ} _ Γ@(_ ◃ _)) ne = τ ⋆ (Ctxt-to-⋆ Γ ne)

_ : ∀ {σ₁ σ₂ σ₃ : Ty} {x : ConTy σ₁} {y : ConTy σ₂} {z : ConTy σ₃} 
    → Ctxt-to-⋆ (x ◃ y ◃ z ◃ ⊘) ne ≡ σ₁ ⋆ (σ₂ ⋆ σ₃)
_ = refl
-}



{-
module _ {P : ConPair → Set} where
  open import Data.Product

  mapCtxtP : (Γ : Ctxt) → All P Γ → ((Σ ConPair P) → ConPair) → Ctxt
  mapCtxtP ⊘ ⊘ _ = ⊘
  mapCtxtP (x ◃ Γ) (p ◂ all) f = f (x , p) ◃ mapCtxtP Γ all f
-}


{-
module _ (F : ConTy _ → ConTy _) where
  data _⊆ᵖ_ : Ctxt → Ctxt → Set where
    empt : ⊘ ⊆ᵖ Γ
    drop : ∀ {x : ConTy τ} → Δ ⊆ᵖ Γ →        Δ  ⊆ᵖ (x ◃ Γ)
    here : ∀ {x : ConTy τ} → Δ ⊆ᵖ Γ → (F x ◃ Δ) ⊆ᵖ (x ◃ Γ)
-}


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

-- Need to use contexts instead, need to get ⊆ relations right

-- A Arithmetic operation operates within a context which it cannot extend 
-- or reduce.
-- This current definition however allows CtxtArit to return ANY type 
-- This also doesn't make great use of contexts (or use of at all)
data CtxtArit (Γ : Ctxt) : Ty → Set where
  var : Γ ∋ τ → CtxtArit Γ τ
  lam : CtxtArit (τ ◃ Γ) σ → CtxtArit Γ (τ ⇒ σ)
  app : CtxtArit Γ (σ ⇒ τ) → CtxtArit Γ σ → CtxtArit Γ τ

  sizeN : CtxtArit Γ (ix s) → CtxtArit Γ N
  posiN : CtxtArit Γ (ix s) → Reshape p s → CtxtArit Γ N
  spliₗ : CtxtArit Γ (ix (s ⊗ p)) → CtxtArit Γ (ix s)
  spliᵣ : CtxtArit Γ (ix (s ⊗ p)) → CtxtArit Γ (ix p)

  _*N_ : CtxtArit Γ N → CtxtArit Γ N → CtxtArit Γ N 

  _*C_ : CtxtArit Γ C → CtxtArit Γ C → CtxtArit Γ C 
  ω`   : CtxtArit Γ N → CtxtArit Γ N → CtxtArit Γ C

  toC  : CtxtArit Γ R → CtxtArit Γ R → CtxtArit Γ C
  toRᵣ : CtxtArit Γ C → CtxtArit Γ R
  toRᵢ : CtxtArit Γ C → CtxtArit Γ R

  to-⋆     : CtxtArit Γ τ → CtxtArit Γ σ → CtxtArit Γ (τ ⋆ σ)
  ⋆-proj₁ : CtxtArit Γ (τ ⋆ σ) → CtxtArit Γ τ
  ⋆-proj₂ : CtxtArit Γ (τ ⋆ σ) → CtxtArit Γ σ
  
  _*R_ : CtxtArit Γ R → CtxtArit Γ R → CtxtArit Γ R 
  _+R_ : CtxtArit Γ R → CtxtArit Γ R → CtxtArit Γ R 
  _-R_ : CtxtArit Γ R → CtxtArit Γ R → CtxtArit Γ R 

  repeat       : (n : ℕ) → CtxtArit Γ R → CtxtArit Γ ℝ

  SIMD-*R      : {n : ℕ} → CtxtArit Γ ℝ → CtxtArit Γ ℝ → CtxtArit Γ ℝ
  SIMD-+R      : {n : ℕ} → CtxtArit Γ ℝ → CtxtArit Γ ℝ → CtxtArit Γ ℝ
  SIMD--R      : {n : ℕ} → CtxtArit Γ ℝ → CtxtArit Γ ℝ → CtxtArit Γ ℝ
  {-
    Here we can just use to-⋆ to make a pair of ℝ

  SIMD-to-⋆    : {n : ℕ} → CtxtArit Γ (τ ◎ n) → CtxtArit Γ (σ ◎ n) → CtxtArit Γ (τ ⋆ σ ◎ n)
  SIMD-⋆-proj₁ : {n : ℕ} → CtxtArit Γ (τ ⋆ σ ◎ n)  → CtxtArit Γ (τ ◎ n)
  SIMD-⋆-proj₂ : {n : ℕ} → CtxtArit Γ (τ ⋆ σ ◎ n)  → CtxtArit Γ (σ ◎ n)
  -}

  ωr`  : CtxtArit Γ N → CtxtArit Γ N → CtxtArit Γ R
  ωi`  : CtxtArit Γ N → CtxtArit Γ N → CtxtArit Γ R
```

```agda  

mult : (a b c d : CtxtArit Γ R) → CtxtArit Γ (R ⋆ R)
mult a b c d = to-⋆ ((a *R c) -R (b *R d)) ((a *R d) +R (b *R c)) 

{-
SIMD-mult : {n : ℕ} {Γ : Ty → Set} (a b c d : CtxtArit Γ (R ◎ n)) → CtxtArit Γ (R ⋆ R ◎ n)
SIMD-mult a b c d = SIMD-to-⋆ (SIMD--R (SIMD-*R a c) (SIMD-*R b d)) (SIMD-+R (SIMD-*R a d) (SIMD-*R b c))
-}

curry : ∀ { X : Set } → (CtxtArit Γ (R ⋆ R) → X) → (CtxtArit Γ R → CtxtArit Γ R → X)
curry f r i = f (to-⋆ r i)

{-
SIMD-curry : ∀ {n : ℕ} {Γ : Ty → Set} → ∀ { X : Set } → (CtxtArit Γ (R ⋆ R ◎ n) → X) → (CtxtArit Γ (R ◎ n) → CtxtArit Γ (R ◎ n) → X)
SIMD-curry f r i = f (SIMD-to-⋆ r i)
-}

uncurry : ∀ { X : Set } → (CtxtArit Γ R → CtxtArit Γ R → X) → (CtxtArit Γ (R ⋆ R) → X)
uncurry f x = f (⋆-proj₁ x) (⋆-proj₂ x)

```

# Issue: Passing Arit to Inp
Currently facing the issue, of trying to work out how to pass an Arit operation 
to Inp for imap, mapsum, and anywhere else. 

For these operations, we are going to define them over a context Δ which is a 
⊆ of the main context Γ. We currently use All to declare that this context Δ 
only contains Arrays. This is working out to be pretty shit.

What if I instead used some kind of method similar to ∋ which lets me give 
(for each element we extract) a predicate and our Arit, which is also just 
another Predicate type which additionally takes evidence of the prior predicate!
```agda
data EachArit (P : Ty → Set) (Op : (τ : Ty) → P τ → Set) : Ctxt → Set where
  empt : EachArit _ _ ⊘
  there : EachArit P Op      Γ                         → EachArit _ _ (τ ◃ Γ)
  here  : EachArit P Op Γ → (τₚ : P τ) → Op τ τₚ → EachArit _ _ (τ ◃ Γ)
```
Is there any way I could make this nicer?

# The set of in place operations

We can then define the set of In-Place operations `Inp`.

We restrict these to currently operate over one shape level `l`
```agda
module _ where
  infixl 2 _>>>_
```
When we define this set of new inplace operations, we want to restrict our 
Contexts to only contain the types we can actually work with 

```agda
  data NewInp : (Γ Δ : Ctxt) → Set where
    compose : NewInp Γ Φ
            → NewInp Φ Δ
            → NewInp Γ Δ

    
    -- Generalised imap where every operation can also access the elements at 
    -- the simultanious operations (Meaning we will need to make use of temporary variables)
    imap` : ∀ {Γ : Ctxt}
          → ∀ {ℓ : L} (s : S ℓ)
          --→ (sub : (λ τ → Σ (Arr τ) λ{(ARR {s = p} τₙ) → Reshape s p }) ∶ Δ ⊆ₚ Γ) -- Extract a sub array and ensure all the shapes have a
            --→ All (λ τ → (Σ (Arr τ) (λ{(ARR {_} {_} {p} _) → Reshape s p}))) Δ -- We can only imap over Arrays
          --→ ? -- All of these arrays must have a reshape into s
          --→ All ? Δ -- For each of these arrays we need the operation
          --→ ? --→ All (Reshape s ∘ ConPair-Shape) Δ
          --→ ? --→ All (λ conPair → Arit Sem (allTys Δ ((ix (ConPair-Shape conPair)) ⇒ ConPair-τ conPair))) Δ
            --→ All (λ τ → CtxtArit (ix s ◃ Δ) τ) Δ -- Could I get away with this???
          -- Fairly nice compared to some of the other options
          → EachArit (λ τ → (Σ (Arr τ) (λ{(ARR {_} {_} {p} _) → Reshape s p}))) 
                     (λ{ (.(ix _) ⇒ τ) (ARR {s = p} num ,ₚ r) → CtxtArit (ix p ◃ Γ) τ })
                      Γ
          → NewInp Γ Γ

    mapSum` : ∀ {Γ Δ : Ctxt} 
            → Δ ⊆ᶜ Γ
            → ∀ {u : ℕ}
            → All (λ τ → (Σ (Arr τ) (λ{(ARR {_} {_} {p} _) → Reshape (ι (ν u)) p}))) Δ -- All (Reshape (ι (ν u)) ∘ ConPair-Shape) Δ
            --→ ∀ {Sem : Ty → Set}
            → All (λ τ → CtxtArit Δ (ix (ι (ν u)) ⇒ ix (ι (ν u)) ⇒ τ)) Δ -- All (λ conPair → Arit Sem (allTys Δ (ix (ι (ν u)) ⇒ ix (ι (ν u)) ⇒ ConPair-τ conPair))) Δ
            → NewInp Γ Γ

    copyOut` : {Γ Δ : Ctxt} 
             → ? -- → _⊆ᵖ_ (λ conPair → [ (ConPair-Num conPair) , s ] ) Δ Γ
             → (s : S (ss l))
             → ? -- → All (λ conPair → Reshape s (ConPair-Shape conPair)) Δ
             → ? -- → All (λ conPair → Reshape (ConPair-Shape conPair) s) Δ
             → NewInp Δ Δ
             → NewInp Γ Γ
    
    -- The easiest form of part is where every Ar in Δ is of the same Shape
    part` : ∀ {Γ Δ : Ctxt}
          --→ Δ ⊆ᶜ Γ
          → {ℓ : L} (s p : S (ss ℓ))
          → ? 
          -- (reshapeableS : All (λ conPair → ∃ λ p → Σ (Reshape s p) λ r → p ⊂ ConPair-Shape conPair) Δ)
          → ? 
          --let Φ = mapCtxtP Δ reshapeableS λ{(conPair ,ₚ _ ,ₚ _ ,ₚ sub) → [ ConPair-Num conPair , (inv-⊂ sub) ] } in NewInp Sem Φ Φ
          → NewInp Γ Γ
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


    {-
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
    -}
```

Within these in place operations, we can then represent twiddles...


```agda
infix 3 there
-- Should be the other way round, but causes an __impossible__ error on my version of agda
--syntax here = name
--syntax b = there here
--syntax i₂ = there (there here)
--syntax i₃ = there there there here
--syntax i₄ = there there there there here

twid` : {s s′ p p′ : S (ss l)} → (r₁ : Reshape s′ s) → (r₂ : Reshape p′ p) → NewInp ((ix (s ⊗ p) ⇒ R) ◃ (ix (s ⊗ p) ⇒ R) ◃ ⊘) _
twid` {l} {s} {s′} {p} {p′} r₁ r₂ =
  imap`
    (s ⊗ p)
    (here (here empt 
      --- This is still not nice
        -- Ideally, some way of tagging variables would be nice so debrunj
      (ARR (Scl R) ,ₚ eq) (⋆-proj₁ (mult (app (var ?) (var ?)) (app (var (there (there here))) (var here)) ? ?))) 
      (ARR (Scl R) ,ₚ eq) ?)

{-
twid` : {s s′ p p′ : S (ss l)} {Sem : Ty → Set} → (r₁ : Reshape s′ s) → (r₂ : Reshape p′ p) → Inp Sem (s ⊗ p) (Scl C)
twid` {l} {s} {s′} {p} {p′} r₁ r₂ = 
      imap`
        (`λ i ⇒ `λ x ⇒ 
          (var x) *C
          ω` 
            (sizeN $ var i) 
            ((posiN (spliₗ $ var $ i) r₁) *N (posiN (spliᵣ $ var $ i) r₂))
        )
-}
{-

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
-}
```
