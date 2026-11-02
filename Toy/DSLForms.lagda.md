<!--
```agda
module Toy.DSLForms where

open import Data.String
open import Data.Nat using (ℕ)
open import Data.Bool renaming (Bool to 𝔹)

```
--!>

When writing a DSL and accompanying trans/compiler in Agda, there are few forms 
it can take. In this file I aim to discuss the different forms such DSLs take, 
and will compare and contrast the differences between them.

# General layout



# Untyped DSL

This is the most simple form of DSL, and contains no typing information

```agda
module Untyped where
  ID : Set
  ID = String

  data DSL : Set where
    lam : (ID → DSL) → DSL
    app : DSL → DSL → DSL
    var : ID → DSL
```
We can see below, that when we try to define the SKI combinator calculus in 
this DSL, we get no typing information or hints - we can apply anything to 
anything else - not good 
```agda
  module SKI where
    -- S x y z = xz(yz)
    S : DSL
    -- K x y = x
    K : DSL
    -- I x = x
    I : DSL

    S = lam λ x → lam λ y → lam λ z → app (app (var x) (var z)) (app (var y) (var z))
    K = lam λ x → lam λ y → var x
    I = lam λ x → var x
```

# Simply typed

To improve on this, we can give ourselves a type system, we will use the same 
`Ty` type from now on, so will define it once for brevity

```agda
module _ where
  data Ty : Set where
    X : Ty
    Y : Ty
    _⇒_ : Ty → Ty → Ty

  infixr 6 _⇒_

  variable
    τ σ δ : Ty
```


```agda

module SimplyTyped where
  ID : Set
  ID = String

  data DSL : Ty → Set where
    var : ID → DSL τ
    lam : (ID → DSL τ) → DSL (σ ⇒ τ)
    app : DSL (σ ⇒ τ) → DSL σ → DSL τ
```

Now we can start giving typing hints when we try to define our SKI calculus, 
but our language still can't carry what the type of variables is - see S
```agda
  module SKI where
    -- S x y z = xz(yz)
    S : DSL ((τ ⇒ σ ⇒ δ) ⇒ (τ ⇒ σ) ⇒ τ ⇒ δ)
    -- K x y = x
    K : DSL (τ ⇒ σ ⇒ τ)
    -- I x = x
    I : DSL (τ ⇒ τ)

    S = lam λ x → lam λ y → lam λ z → app (app (var x) (var z)) (app (var y) (var z))
    K = lam λ x → lam λ y → var x
    I = lam λ x → var x
```

One of the problems we have here, is that for a given ID, we don't know what 
its type is.

# Simply Typed with semantics

```agda
module Semantics where
  data DSL (Sem : Ty → Set) : Ty → Set where
    var : Sem τ → DSL Sem τ
    lam : (Sem τ → DSL Sem σ) → DSL Sem (τ ⇒ σ)
    app : DSL Sem (σ ⇒ τ) → DSL Sem σ → DSL Sem τ
```
Now, when we go to define SKI calculus, our variables are given types, and we 
will get a type error if we use them wrong
```agda
  module SKI (Sem : Ty → Set) where
    -- S x y z = xz(yz)
    S : DSL Sem ((τ ⇒ σ ⇒ δ) ⇒ (τ ⇒ σ) ⇒ τ ⇒ δ)
    -- K x y = x
    K : DSL Sem (τ ⇒ σ ⇒ τ)
    -- I x = x
    I : DSL Sem (τ ⇒ τ)

    S = lam λ x → lam λ y → lam λ z → app (app (var x) (var z)) (app (var y) (var z))
    K = lam λ x → lam λ y → var x
    I = lam λ x → var x
```

When we then want to compile, we simply need to define what our Semantics are
```agda
  module Compile where
    Sem : Ty → Set
    Sem (x ⇒ y) = Sem x → Sem y
    Sem X = 𝔹
    Sem Y = ℕ

    toAgda : DSL Sem τ → Sem τ
    toAgda (var x) = x
    toAgda (lam x) y = toAgda (x y)
    toAgda (app x y) = (toAgda x) (toAgda y)
```

# Simply Typed with Context

An approach which is alternate to Semantics is Context
```agda 
module Contexts where
  data Ctxt : Set where
    ⊘ : Ctxt
    _◃_ : Ty → Ctxt → Ctxt

  variable
    Γ Δ : Ctxt

  data _∋_ : Ctxt → Ty → Set where
    here : (τ ◃ Γ) ∋ τ
    there : Γ ∋ τ → (σ ◃ Γ) ∋ τ

  data DSL (Γ : Ctxt) : Ty → Set where
    var : Γ ∋ τ → DSL Γ τ
    lam : DSL (τ ◃ Γ) σ → DSL Γ (τ ⇒ σ)
    app : DSL Γ (σ ⇒ τ) → DSL Γ σ → DSL Γ τ

  module SKI (Γ : Ctxt) where
    -- S x y z = xz(yz)
    S : DSL Γ ((τ ⇒ σ ⇒ δ) ⇒ (τ ⇒ σ) ⇒ τ ⇒ δ)
    -- K x y = x
    K : DSL Γ (τ ⇒ σ ⇒ τ)
    -- I x = x
    I : DSL Γ (τ ⇒ τ)

    S = lam (lam (lam (app (app (var (there (there here))) (var here)) (app (var (there here)) (var here)))))
    K = lam (lam (var (there here)))
    I = lam (var here)
```

To compile, we first need to create a structure with which we hold our 
contexts memory, we can then give this semantics and compile nicely

```agda
  
  module Compile where
    module CtxtSem (Sem : Ty → Set) where
      data CtxtVal : Ctxt → Set where
        ⊘ : CtxtVal ⊘
        _◃_ : Sem τ → CtxtVal Γ → CtxtVal (τ ◃ Γ)

      pull : CtxtVal Γ → Γ ∋ τ → Sem τ
      pull (x ◃ _) here = x
      pull (_ ◃ Γ) (there ni) = pull Γ ni
    
    -- We still need to give some kind of meaning (or.... semantics) to Ty
    Sem : Ty → Set
    Sem (x ⇒ y) = Sem x → Sem y
    Sem X = 𝔹
    Sem Y = ℕ
    open CtxtSem Sem

    -- But we also need to have some idea of what is in our context Γ...
    toAgda : CtxtVal Γ → DSL Γ τ → Sem τ
    toAgda Γ (var x) = pull Γ x
    toAgda Γ (lam x) y = toAgda (y ◃ Γ) x
    toAgda Γ (app x y) = (toAgda Γ x) (toAgda Γ y)
```
