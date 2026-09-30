Here I define the translation from the DSL into C...
```agda
--{-# OPTIONS --termination-depth 40 #-}

module CodeGeneration.Translate-C where
open import Function 
open import Matrix.Mon
open import Matrix.NatMon

open import Matrix.Leveled.Base ℕ-Mon
open import Matrix.Leveled.Reshape ℕ-Mon
open import Matrix.Leveled.Change-Major ℕ-Mon
open import Matrix.Leveled.SubShape ℕ-Mon
open import Matrix.Leveled.NatMon-Change-Major

open import Data.Nat hiding (_≟_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String hiding (length)
open import Data.Product hiding (swap)
open import Data.Maybe renaming (_>>=_ to _⟫=_; zip to zipM) 
open import Data.Bool hiding (_≟_)

open import Relation.Binary.PropositionalEquality

open import Text.Printf

open import CodeGeneration.DSL

private variable
  τ σ : Ty
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : L
  s s′ k : S ℓ
  r : Reshape s s′
  n : ℕ
```

We can now start looking at generating some C code.
While doing this I will use the state monad, which will allow me to safely 
create new variable (names). We also define here a helper `fresh-var` function
to create an unused variable name.
```agda
open import Effect.Monad
open import Effect.Monad.State
open RawMonadState {{...}}
open RawMonad {{...}} hiding (_⊗_)
instance
  _ = monad
  _ = monadState 

show-var : ℕ → String
show-var = printf "x_%u"

fresh-var : State ℕ String
fresh-var = do
  n ← get
  modify suc
  return $ show-var n
```

# Length helper

We then need a small helper to get the length of shapes, this needs `suc` as we
treat `ν` as `Fin ∘ suc`
```agda
clen : S ℓ → ℕ
clen = suc ∘ length
```


# Indices
```agda
module _ where
```
To represent indices I need to create a representation of indexes where each 
leaf of the shape tree is a variable (or stringified operation).

```agda
  data Ix : S ℓ → Set where
    ν : ∀ {n : ℕ} → String → Ix (ν n)
    ι : ∀ {s : S ℓ} → Ix s → Ix (ι s)
    _⊗_ : ∀ {s p : S (ss ℓ)} → Ix s → Ix p → Ix (s ⊗ p)

```

For this Ix type I create a function to make an Ix instance where every leaf 
is a new variable (for use when generating loop nests).
```agda
  new-Ix : ∀ (s : S ℓ) → State ℕ (Ix s)
  new-Ix (ν n) = do
      ix-n ← fresh-var
      return (ν ix-n)
  new-Ix (ι s) = do
      ix-s ← new-Ix s
      return (ι ix-s)
  new-Ix (s ⊗ p) = do
      ix-s ← new-Ix s
      ix-p ← new-Ix p
      return (ix-s ⊗ ix-p)
```

We also need a way to reshape IX then get the flat position.
We can also then create a function to get this position after a reshape has been applied
```agda
  ix-flat-index : ∀ {n : ℕ} → Ix (ν n) → String
  ix-flat-index (ν i) = i
```

```agda
  NormResh : Reshape s s′ → Reshape s s′
  NormResh eq = eq
  NormResh (r₁ ∙ r₂) with NormResh r₁ 
  NormResh (r₁ ∙ r₂) | eq with NormResh r₂
  NormResh (r₁ ∙ r₂) | eq | eq = eq
  NormResh (r₁ ∙ r₂) | eq | b = b
  NormResh (r₁ ∙ r₂) | a  with NormResh r₂
  NormResh (r₁ ∙ r₂) | a | eq = a
  --NormResh (r₁ ∙ r₂) | flat | unflat = eq
  --NormResh (r₁ ∙ r₂) | unflat | flat = eq -- Need to also split on s/s′
  NormResh (r₁ ∙ r₂) | swap | swap = eq
  NormResh (r₁ ∙ r₂) | assoₗ | assoᵣ = eq 
  NormResh (r₁ ∙ r₂) | assoᵣ | assoₗ = eq 
  NormResh (r₁ ∙ r₂) | up eq | down eq = eq
  NormResh (r₁ ∙ r₂) | a | b = a ∙ b
  NormResh (r₁ ⊕ r₂) with NormResh r₁ | NormResh r₂
  ... | eq | eq  = eq
  ... | a  | b  = a ⊕ b
  NormResh (up r) = up (NormResh r)
  NormResh (down r) = down (NormResh r)
  NormResh flat = flat
  NormResh unflat = unflat
  NormResh swap = swap
  NormResh assoₗ = assoₗ
  NormResh assoᵣ = assoᵣ

  -- Helper for debugging what RESH should be doing
  showResh′ : Reshape s s′ → String
  showResh′ eq = "eq"
  showResh′ (r₁ ∙ r₂) = parens $ (showResh′ r₁) <+> "∙" <+> (showResh′ r₂)
  showResh′ (r₁ ⊕ r₂) = parens $ (showResh′ r₁) <+> "⊕" <+> (showResh′ r₂)
  showResh′ (up   r) = parens $ "up"   <+> showResh′ r
  showResh′ (down r) = parens $ "down" <+> showResh′ r
  showResh′ flat = "flat"
  showResh′ unflat = "unflat"
  showResh′ swap = "swap"
  showResh′ assoₗ = "assol"
  showResh′ assoᵣ = "assor"

  showResh : Reshape s s′ → String
  showResh = showResh′ ∘ NormResh
```

I had the thought of creating a small dsl for pointer arithmetic to make it 
harder to cock up, but I think I'm being a bit thick atm trying to convert ix 
to a pointer representation
```agda
  resh-ix : ∀ {ℓ ℓ′ : L} {s : S ℓ} {s′ : S ℓ′} → Reshape s s′ → Ix s → Ix s′
  resh-ix eq i = i
  resh-ix (r ∙ r₁) i = resh-ix r (resh-ix r₁ i)
  resh-ix (r ⊕ r₁) (i ⊗ j) = resh-ix r i ⊗ resh-ix r₁ j
  resh-ix (up r) i = ι (resh-ix r i)
  resh-ix (down r) (ι i) = resh-ix r i
  resh-ix swap (i ⊗ j) = j ⊗ i
  resh-ix assoₗ ((i₁ ⊗ i₂) ⊗ i₃) = i₁ ⊗ (i₂ ⊗ i₃)
  resh-ix assoᵣ (i₁ ⊗ (i₂ ⊗ i₃)) = (i₁ ⊗ i₂) ⊗ i₃
  -- These need mod, just needs a moment of thinking
  resh-ix (flat {m} {n}) (ι (ν i) ⊗ ι (ν j)) = ν (printf "((%u * %s) + %s)" (suc n) i j)
  resh-ix (unflat {m} {n}) (ν x) = ι (ν (printf "(%s / %u)" x (suc n) )) ⊗ ι (ν (printf "(%s %% %u)" x (suc n)))
```

We then create a converter from ix to subscripts to allow us to stringify them.
```agda
  ix-to-subscripts : Ix s → String
  ix-to-subscripts (ν i) = "[" ++ i ++ "]"
  ix-to-subscripts (ι i) = ix-to-subscripts i
  ix-to-subscripts (i ⊗ j) = ix-to-subscripts i ++ ix-to-subscripts j

  ix-to-str : Ix s → String → String
  ix-to-str i name = "(*" ++ name ++ ")" ++ (ix-to-subscripts i)

```

# Arithmetic Evaluator
We can then create an evaluator and translator for our Airthmetic operations.
Our evaluator is going to evaluate all lambda calculus, while the translator 
will stringify this into something which can be used in C. 

```agda
open import Data.List.Base as List renaming (_++_ to _++ₗ_; [_] to [_]ₗ; map to mapₗ) hiding (intersperse)
module _ where

  data NOp : Set where
    var : String → NOp
    Nconst : ℕ → NOp
    Niota : Ix (ν n) → NOp
    Nmult : NOp → NOp → NOp
      
  mutual
    data COp : Set where
      var : String → COp
      Cmult : COp → COp → COp
      ω : NOp → NOp → COp
      fromR : ROp → ROp → COp

    data ROp : Set where
      var : String → ROp
      Rmult : ROp → ROp → ROp
      Rplus : ROp → ROp → ROp
      Rminu : ROp → ROp → ROp
      Rωr : NOp → NOp → ROp
      Rωi : NOp → NOp → ROp
      fromCr : COp → ROp
      fromCi : COp → ROp

  translate-Ty : (τ : Ty) → Set
  translate-Ty C = COp
  translate-Ty R = ROp
  translate-Ty N = NOp
  translate-Ty (ix s) = Ix s
  translate-Ty (τ ⇒ σ) = translate-Ty τ → State ℕ (translate-Ty σ)
  translate-Ty (τ ⋆ σ) = translate-Ty τ × translate-Ty σ

  SclOp : ∀ {τ} → Scalar τ → Set
  SclOp {τ} _ = translate-Ty τ

  SclVar : ∀ {τ} → (scl : Scalar τ) → (String → SclOp scl)
  SclVar C = var
  SclVar R = var
  SclVar N = var

  data AssignmentOperation : Set where
    ≔ : AssignmentOperation
    += : AssignmentOperation

  mutual
    data Instruction : Set where
      comment′ : String → Instruction
      assign′ : String → AssignmentOperation → {scl : Scalar τ} → SclOp scl → Instruction
      declare′ : String → S ℓ → Scalar τ → Instruction
      declareScl′ : String → Scalar τ → Instruction
      loop′ : Ix s → Program → Instruction
      free′ : String → Instruction

    Program : Set
    Program = List Instruction

  arit-eval : ∀ {τ : Ty} → Arit translate-Ty τ → State ℕ (translate-Ty τ)
  arit-eval (var x) = return x
  arit-eval (lam x) = return (arit-eval ∘ x) 
  arit-eval (app f x) = do
    f′ ← arit-eval f
    x′ ← arit-eval x
    f′ x′
  arit-eval (sizeN {s = s} _) = return $ Nconst (clen s)
  arit-eval (posiN i r) = do
    i′ ← arit-eval i
    return $ Niota $ resh-ix (ν-flattenᵣ ∙ rev r) i′
  arit-eval (spliₗ x) = do
    (i ⊗ _) ← arit-eval x
    return i
  arit-eval (spliᵣ x) = do
    (_ ⊗ i) ← arit-eval x
    return i
  arit-eval (x *N y) = do
    x′ ← arit-eval x
    y′ ← arit-eval y
    return $ Nmult x′ y′
  arit-eval (x *C y) = do
    x′ ← arit-eval x
    y′ ← arit-eval y
    return $ Cmult x′ y′
  arit-eval (ω` x y) = do
    x′ ← arit-eval x
    y′ ← arit-eval y
    return $ ω x′ y′
  arit-eval (toC r i) = do
    r′ ← arit-eval r
    i′ ← arit-eval i
    return $ fromR r′ i′
  arit-eval (toRᵣ x) = do
    x′ ← arit-eval x
    return $ fromCr x′
  arit-eval (toRᵢ x) = do
    x′ ← arit-eval x
    return $ fromCi x′
  arit-eval (to-⋆ x y) = do
    x′ ← arit-eval x
    y′ ← arit-eval y
    return $ x′ , y′
  arit-eval (⋆-proj₁ x) = do 
    x₁ , _  ← arit-eval x
    return x₁
  arit-eval (⋆-proj₂ x) = do
    _  , x₂ ← arit-eval x
    return x₂
  arit-eval (x *R y) = do
    x′ ← arit-eval x
    y′ ← arit-eval y
    return $ Rmult x′ y′
  arit-eval (x +R y) = do
    x′ ← arit-eval x
    y′ ← arit-eval y
    return $ Rplus x′ y′
  arit-eval (x -R y) = do
    x′ ← arit-eval x
    y′ ← arit-eval y
    return $ Rminu x′ y′
  arit-eval (ωr` n i) = do
    n′ ← arit-eval n
    i′ ← arit-eval i
    return $ Rωr n′ i′
  arit-eval (ωi` n i) = do
    n′ ← arit-eval n
    i′ ← arit-eval i
    return $ Rωi n′ i′
```

# C Helpers

We can then define a set of functions which spit out some common C strings for 
us. These lay out a structure for the eventual C dsl


```agda
module _ where
  num-tuple : Set → Num τ → Set
  num-tuple X (x ⋆ y) = num-tuple X x × num-tuple X y
  num-tuple X _ = X

  fresh-vars : (α : Num τ) → State ℕ (num-tuple String α)
  fresh-vars (Scl x) = fresh-var
  fresh-vars (α₁ ⋆ α₂) = do 
    l ← fresh-vars α₁
    r ← fresh-vars α₂
    return $ l , r

  pull-⋆ : {A : Set} (α : Num τ) → num-tuple (A → String) α → A → translate-Ty τ
  pull-⋆ (Scl α) xs i = SclVar α (xs i)
  pull-⋆ (α₁ ⋆ α₂) (xs , ys) i = (pull-⋆ α₁ xs i) , (pull-⋆ α₂ ys i)

  num-map : ∀ {A B : Set} (α : Num τ) → (A → B) → num-tuple A α → num-tuple B α
  num-map (Scl x) f xs = f xs
  num-map (α₁  ⋆ α₂) f (xs , ys) = num-map α₁ f xs , num-map α₂ f ys

  create-ass′ : ∀ {A : Set} (α : Num τ) → AssignmentOperation → num-tuple (A → String) α → translate-Ty τ → A → Program
  create-ass′ (Scl α) op xs ys i = [ assign′ (xs i) op {α} ys ]ₗ
  create-ass′ (α₁ ⋆ α₂) op (xs₁ , xs₂) (ys₁ , ys₂) i = 
            create-ass′ α₁ op xs₁ ys₁ i 
        ++ₗ create-ass′ α₂ op xs₂ ys₂ i

  num-tuple→translate-Ty : {α : Num τ} → num-tuple String α → translate-Ty τ
  num-tuple→translate-Ty {_} {Scl α} x = SclVar α x
  num-tuple→translate-Ty {.(_ ⋆ _)} {α₁ ⋆ α₂} (xs₁ , xs₂) = num-tuple→translate-Ty xs₁ , num-tuple→translate-Ty xs₂

  -- The below is a horible implementation which works, I now need to make this nice :)
  -- Create arse needs to take up two parts, the arse into temporary variables, 
  -- and the arse back into the in place memory location
  -- (But maybe not always)
  create-ass : ∀ {X : Set}
             → ∀ (α : Num τ) 
             → AssignmentOperation 
             → num-tuple (X → String) α 
             → translate-Ty τ 
             → X
             → State ℕ (Program × Program)
  create-ass {X = X} α op xs ys i = do
    tmp-vars′ ← fresh-vars α
    let tmp-vars = num-map α (λ x → λ _ → x) (tmp-vars′) 
    return $ declare-tmp-vars α tmp-vars′ , create-tmp-ass tmp-vars ++ₗ create-ass-from-tmp (tmp-vars′)
    where
      declare-tmp-vars : (β : Num σ) → (num-tuple String β) → Program
      declare-tmp-vars (Scl β) zs = [ declareScl′ zs β ]ₗ
      declare-tmp-vars (β₁ ⋆ β₂) (zs₁ , zs₂) = declare-tmp-vars β₁ zs₁ 
                                           ++ₗ declare-tmp-vars β₂ zs₂

      create-tmp-ass : (num-tuple (_ → String) α) → Program
      create-tmp-ass zs = create-ass′ α ≔ zs ys i

      create-ass-from-tmp : (num-tuple String α) → Program
      create-ass-from-tmp zs = create-ass′ α op xs (num-tuple→translate-Ty zs) i
  {-
  create-ass : ∀ {A : Set} (α : Num τ) → AssignmentOperation → num-tuple (A → String) α → translate-Ty τ → A → Program
  create-ass (Scl α) op xs ys i = [ assign′ (xs i) op {α} ys ]ₗ
  create-ass (α₁ ⋆ α₂) op (xs₁ , xs₂) (ys₁ , ys₂) i = create-ass α₁ op xs₁ ys₁ i ++ₗ create-ass α₂ op xs₂ ys₂ i
  -}

  num-i-to-prog : {α : Num τ} → num-tuple Instruction α → Program
  num-i-to-prog {α = Scl α} = [_]ₗ
  num-i-to-prog {α = α₁ ⋆ α₂} (l , r) = num-i-to-prog l ++ₗ num-i-to-prog r

  num-tuple-distrib : ∀ {A B : Set} → (α : Num τ) → num-tuple (A × B) α → num-tuple A α × num-tuple B α
  num-tuple-distrib (Scl _) x = x
  num-tuple-distrib (α₁ ⋆ α₂) (x , y) = 
    let a , b = num-tuple-distrib α₁ x in
    let c , d = num-tuple-distrib α₂ y in
    (a , c) , (b , d)

  num-tuple-distrib₃ : ∀ {A B C : Set} → (α : Num τ) → num-tuple (A × B × C) α → num-tuple A α × num-tuple B α × num-tuple C α
  num-tuple-distrib₃ α xs = 
    let a , x = num-tuple-distrib α xs in
    let b , c = num-tuple-distrib α x  in
    a , b , c 

module _ where
  natural-type : String
  natural-type = "unsigned"

  real-type : String
  real-type = "real"

  complex-type : String
  complex-type = "complex" <+> real-type

  Scl-type : ∀ {τ : Ty} → Scalar τ → String
  Scl-type C = complex-type
  Scl-type R = real-type
  Scl-type N = natural-type

  calloc-op : (type : String) → ℕ → String
  calloc-op ty s = printf "calloc(%u, sizeof(%s))" s ty

  for-template : String → ℕ → String → String
  for-template i n expr = printf "for (size_t %s = 0; %s < %u; %s++) {\n%s}\n" i i n i expr

  loopnest : Ix s → (String → String)
  loopnest {s = ν n} (ν i) = for-template i (suc n)
  loopnest (ι s) = loopnest s
  loopnest (s ⊗ s₁) = loopnest s ∘ loopnest s₁

  ShapeCast′ : Bool → S ℓ → String
  ShapeCast′ isLeft (ι s) = ShapeCast′ isLeft s
  ShapeCast′ isLeft (s₁ ⊗ s₂) = ShapeCast′ isLeft s₁ ++ ShapeCast′ false s₂
  ShapeCast′ false (ν x) = printf "[%u]" (suc x)
  ShapeCast′ true (ν x) = ""

  ShapeCast : S ℓ → String
  ShapeCast = ShapeCast′ false

  ArCast : Maybe String → String → S ℓ → String
  ArCast nothing type = ArCast (just "") type
  ArCast (just memName) type = printf "%s (*%s)%s" type memName ∘ ShapeCast

  commentBlock : String → String → String
  commentBlock comment body = printf "//Start: %s\n%s//End: %s\n" comment body comment

  calloc : Scalar τ → S ℓ → State ℕ (String × Instruction × Instruction)
  calloc scl s = do  
    memName′ ← fresh-var
    let memName = memName′
    let ops = declare′ memName s scl
    let free = free′ memName
    return $ memName , ops , free

  callocs : (α : Num τ) → S ℓ → State ℕ (num-tuple (String × Instruction × Instruction) α)
  callocs (Scl α) = calloc α
  callocs (α₁ ⋆ α₂) s = do
    l ← callocs α₁ s
    r ← callocs α₂ s
    return $ l , r
```
# ROp Equality
One thing I will frequently come accross is the case fromCr (fromR x _) which
we shuld be able to reduce to `x`.
My original thought here was that the operation:
  `_≟ᵣ : (a : ROp) → (b : ROp) → Dec (a ≡ b)`
would allow me to detect these cases, but contructing both proofs of ¬ (a ≡ b),
and `a ≡ b` (if this was changed to a semidecision) does not appear possible 
with the current implementation of ROp (which lacks semantics for fromR/ fromCr)
I may come back to this but am letting it lie for now

```agda
{-
module _ where
  open import Relation.Nullary.Decidable hiding (map′)
  open import Relation.Nullary.Negation
  open import Data.Empty

  -- I propose that I cannot use Dec here because I cannot prove the case where
  -- ¬ x ≡ y → ¬ var x ≡ var y
  _≟ᵣ_ : (a : ROp) → (b : ROp) → Maybe (a ≡ b)
  var x ≟ᵣ var y with x ≟ y
  ... | no ¬a = nothing
  ... | yes refl = just refl
  var x ≟ᵣ Rmult b b₁ = ?
  var x ≟ᵣ Rplus b b₁ = ?
  var x ≟ᵣ Rminu b b₁ = ?
  var x ≟ᵣ Rωr x₁ x₂ = ?
  var x ≟ᵣ Rωi x₁ x₂ = ?
  var x ≟ᵣ fromCr (fromR y _) with  (var x) ≟ᵣ y 
  --- This starts getting dangerous, as I can't construct a proof here as we 
  -- lack semantics for fromR/ fromCr, and so would be resolved to return Bool
  -- which is sketch
  ... | just refl = just ?
  ... | nothing = just ?
  var x ≟ᵣ fromCr (var x₁) = nothing
  var x ≟ᵣ fromCr (Cmult x₁ x₂) = nothing
  var x ≟ᵣ fromCr (ω x₁ x₂) = nothing
  var x ≟ᵣ fromCi x₁ = ?
  Rmult a a₁ ≟ᵣ b = ?
  Rplus a a₁ ≟ᵣ b = ?
  Rminu a a₁ ≟ᵣ b = ?
  Rωr x x₁ ≟ᵣ b = ?
  Rωi x x₁ ≟ᵣ b = ?
  fromCr x ≟ᵣ b = ?
  fromCi x ≟ᵣ b = ?
  -}
```

# C AST

If I create a small AST representing C, then migrating from ℂ to ℝ × ℝ should 
become trivial as we can make the change in the next translation step

```agda
module _ where
  
    
  evaled-to-str : (val : Num τ) → translate-Ty τ → num-tuple String val
  evaled-to-str (Scl C) (var x) = x
  evaled-to-str (Scl C) (Cmult op₁ op₂) = printf "(%s * %s)" (evaled-to-str (Scl C) op₁) (evaled-to-str (Scl C) op₂)
  evaled-to-str (Scl C) (ω op₁ op₂) = printf "minus_omega(%s, %s)" (evaled-to-str (Scl N) op₁) (evaled-to-str (Scl N) op₂)
  evaled-to-str (Scl N) (Nconst x) = showℕ x
  evaled-to-str (Scl N) (Niota (ν i)) = i
  evaled-to-str (Scl N) (Nmult op₁ op₂) = printf "(%s * %s)" (evaled-to-str (Scl N) op₁) (evaled-to-str (Scl N) op₂)
  evaled-to-str (Scl R) (var x) = x
  evaled-to-str (Scl R) (Rmult l r) = printf "(%s * %s)" (evaled-to-str (Scl R) l) (evaled-to-str (Scl R) r)
  evaled-to-str (Scl R) (Rplus l r) = printf "(%s + %s)" (evaled-to-str (Scl R) l) (evaled-to-str (Scl R) r)
  evaled-to-str (Scl R) (Rminu l r) = printf "(%s - %s)" (evaled-to-str (Scl R) l) (evaled-to-str (Scl R) r)
  evaled-to-str (Scl R) (Rωr op₁ op₂) = printf "r_minus_omega(%s, %s)" (evaled-to-str (Scl N) op₁) (evaled-to-str (Scl N) op₂)
  evaled-to-str (Scl R) (Rωi op₁ op₂) = printf "i_minus_omega(%s, %s)" (evaled-to-str (Scl N) op₁) (evaled-to-str (Scl N) op₂)
  -- Small optimisations to remove unessasary computation
  evaled-to-str (Scl R) (fromCr (fromR x _)) = (evaled-to-str (Scl R) x)
  evaled-to-str (Scl R) (fromCr (ω op₁ op₂)) = evaled-to-str (Scl R) (Rωr op₁ op₂)
  evaled-to-str (Scl R) (fromCr x) = printf "(creal %s)" $ evaled-to-str (Scl C) x
  evaled-to-str (Scl R) (fromCi (fromR _ x)) = (evaled-to-str (Scl R) x)
  evaled-to-str (Scl R) (fromCi (ω op₁ op₂)) = evaled-to-str (Scl R) (Rωi op₁ op₂)
  evaled-to-str (Scl R) (fromCi x) = printf "(cimag %s)" $ evaled-to-str (Scl C) x
  -- An optimisation could also be added here to remove `fromR (fromCr x) (fromCi y)` when x ≡ y,
  -- but we would need to check `x ≟ y` 
  evaled-to-str (Scl C) (fromR r i) = printf "(%s + (%s * I))" (evaled-to-str (Scl R) r) (evaled-to-str (Scl R) i)
  evaled-to-str (a ⋆ b) (fst , snd) = (evaled-to-str a fst) , (evaled-to-str b snd)
  evaled-to-str (Scl N) (var x) = x

  showAssignmentOperation : AssignmentOperation → String
  showAssignmentOperation ≔ = "="
  showAssignmentOperation += = "+="

  showNumue : {scl : Scalar τ} → SclOp scl → String
  showNumue {_} {scl} = evaled-to-str (Scl scl)

  map′ : ∀ {A B : Set} → (A → B) → List A → List B
  map′ f []       = []
  map′ f (x ∷ xs) = f x ∷ map′ f xs

  --- THIS IS VERY CHEATY
  {-# TERMINATING #-}
  --- This is less cheaty but not great either
  --{-# NON_TERMINATING #-}
  mutual
    showInstruction : Instruction → String
    showInstruction (comment′ x) = unlines $ List.map ("//" <+>_) $ lines x
    showInstruction (assign′ var′ op′ {scl = scl} val′) = var′ <+> (showAssignmentOperation op′) <+> showNumue {_} {scl} val′
    showInstruction (loop′ i ins) = loopnest i (showProgram ins)
    showInstruction (free′ x) = printf "free(%s)" x
    showInstruction (declare′ memName s scl) = printf "%s = %s" (ArCast (just memName) (Scl-type scl) s) (calloc-op (Scl-type scl) (clen s))
    showInstruction (declareScl′ memName scl) = printf "%s %s" (Scl-type scl) memName

    showProgram  : Program → String
    showProgram = unlines ∘ map′ (_++ ";") ∘ map′ showInstruction 
```


# C Translation

Finally we can move to our C translation

```agda
scl-step : (scl : Scalar τ) → (Ix s → String) → Inp translate-Ty s (Scl scl) → (State ℕ Program)
scl-step scl xs (imap` arit) = do
  i ← new-Ix _
  arit′ ← arit-eval (app (app arit (var i)) (var (SclVar scl (xs i))))
  return $ [ loop′ i [ assign′ (xs i) ≔ {scl} arit′ ]ₗ ]ₗ
scl-step scl xs (compose inp₁ inp₂) = do
  ins₁ ← scl-step scl xs inp₁ 
  ins₂ ← scl-step scl xs inp₂
  return $ ins₁ ++ₗ ins₂
scl-step scl xs (mapSum` {u} arit) = do
  memName , assign , free ← calloc scl (ι (ν u))

  i ← new-Ix (ι (ν u))
  j ← new-Ix (ι (ν u))
  k ← new-Ix (ι (ν u))

  op ← arit-eval $ app (app (app arit (`λ l ⇒ (var (SclVar scl (xs l))))) (var i)) (var j)

  let body = loop′ j [ loop′ i [ assign′ (ix-to-str i memName) += {scl} op ]ₗ ]ₗ

  let copyBack = loop′ k [ assign′ (xs k) ≔ {scl} (SclVar scl (ix-to-str k memName)) ]ₗ
  return $ assign ∷ body ∷ copyBack ∷ [ free ]ₗ
scl-step scl xs (copyOut` {_} {s} {p} r₁ r₃ inp) = do 
  workingMem , assign , free ← calloc scl p

  i ← new-Ix s
  let copyOutOp = comment′ (showResh r₁)
                ∷ [ loop′ i [ assign′ (ix-to-str (resh-ix r₁ i) workingMem) ≔ {scl} (SclVar scl (xs (ι i))) ]ₗ ]ₗ

  op ← scl-step scl (flip ix-to-str workingMem) inp

  j ← new-Ix s
  let copyInOp = comment′ (showResh r₃)
              ∷ [ loop′ j [ assign′ (xs (ι j)) ≔ {scl} (SclVar scl (ix-to-str (resh-ix (rev r₃) j) workingMem)) ]ₗ ]ₗ

  return $ [ assign ]ₗ ++ₗ copyOutOp ++ₗ op ++ₗ copyInOp ++ₗ [ free ]ₗ
scl-step scl xs (part` {_} {s} {p} s⊂p inp) = do
  i ← new-Ix s
  let ys = λ j → xs (resh-ix (rev (to-resh s⊂p)) (i ⊗ j))

  op ← scl-step scl ys inp

  return $ [ loop′ i op ]ₗ

num-step : (num : Num τ) → num-tuple (Ix s → String) num → Inp translate-Ty s num → (State ℕ Program)
num-step α xs (imap` fs) = do
  i ← new-Ix _
  arit ← arit-eval (app (app fs (var i)) (var (pull-⋆ α xs i)))
  dec , ass ← create-ass α ≔ xs arit i
  return $ dec ++ₗ [ loop′ i ass ]ₗ
num-step α xs (compose inp₁ inp₂) = do
  ins₁ ← num-step α xs inp₁ 
  ins₂ ← num-step α xs inp₂
  return $ ins₁ ++ₗ ins₂
num-step α xs (copyOut` {s = s} {p} r₁ r₃ inp) = do
  mem ← callocs α p
  let workingMems , assigns , frees = num-tuple-distrib₃ α mem

  let workingMems′ = num-map _ (flip (ix-to-str {s = p})) workingMems
  let assigns′ = num-i-to-prog assigns
  let frees′   = num-i-to-prog frees

  i ← new-Ix s
  let copyOutOps = comment′ (showResh r₁) ∷ [ loop′ i (create-ass′ α ≔ workingMems′ (pull-⋆ α xs (ι i)) (resh-ix r₁ i)) ]ₗ
  
  ops ← num-step α workingMems′ inp

  j ← new-Ix s
  let copyInOps = comment′ (showResh r₃) ∷ [ loop′ j (create-ass′ α ≔ xs (pull-⋆ α workingMems′ (resh-ix (rev r₃) j)) (ι j)) ]ₗ

  return $ assigns′ ++ₗ copyOutOps ++ₗ ops ++ₗ copyInOps ++ₗ frees′
num-step α xs (part` {_} {s} {p} s⊂p inp) = do
  i ← new-Ix s
  let ys = num-map α (λ ys j → ys (resh-ix (rev (to-resh s⊂p)) (i ⊗ j))) xs
  ops ← num-step α ys inp
  return $ [ loop′ i ops ]ₗ
num-step α xs (mapSum` {u} arit) = do
  mem ← callocs α (ι (ν u))
  let workingMems , assigns , frees = num-tuple-distrib₃ α mem

  let workingMems′ = num-map _ (flip (ix-to-str {s = (ι (ν u))})) workingMems
  let assigns′ = num-i-to-prog assigns
  let frees′   = num-i-to-prog frees

  i ← new-Ix (ι (ν u))
  j ← new-Ix (ι (ν u))
  k ← new-Ix (ι (ν u))
  
  ops ← arit-eval $ app (app (app arit (var (λ δ → return $ pull-⋆ α xs δ))) (var i)) (var j)

  dec , ass ← create-ass α += workingMems′ ops i 
  let body = dec ++ₗ [ loop′ j [ loop′ i ass ]ₗ ]ₗ

  let copyBack = loop′ k $ create-ass′ α ≔ xs (pull-⋆ α workingMems′ k) k

  return $ assigns′ ++ₗ body ++ₗ [ copyBack ]ₗ ++ₗ frees′

{-
-- This would be quite a nice proof, to show that our more complicated step 
-- implementation is eqivilant to our more simple step implementation for scalars...
scl≡num : ∀ (scl : Scalar τ) → (inp : Inp translate-Ty s (Scl scl)) → (xs : Ix s → String) → scl-step scl xs inp ≡ num-step (Scl scl) xs inp
scl≡num scl (compose inp inp₁) xs rewrite scl≡num scl inp xs | scl≡num scl inp₁ xs = refl
scl≡num scl (copyOut` r₁ r₂ inp) xs rewrite scl≡num scl inp _ = ?
scl≡num scl (part` s⊂p inp) xs = ?
scl≡num scl (imap` x) xs = ?
scl≡num scl (mapSum` x) xs = ?
-}

toArgs : {α : Num τ} (s : S ℓ) → num-tuple (Maybe String) α → List String 
toArgs {α = Scl α} s x = [ ArCast x (Scl-type α) s ]ₗ
toArgs {α = _ ⋆ _} s (xs , ys) = toArgs s xs ++ₗ toArgs s ys

nothing-num-tuple : {A : Set} (α : Num τ) → num-tuple (Maybe A) α
nothing-num-tuple (Scl _) = nothing
nothing-num-tuple (_ ⋆ _) = nothing-num-tuple _ , nothing-num-tuple _

inp→f : (α : Num τ) → Inp translate-Ty s α → String → String
inp→f {s = s} α inp function-name  = runState inp→f′ 0 .proj₂
  where
    inp→f′ : State ℕ String
    inp→f′ = do
      var-names ← fresh-vars α
      let var-names′ = num-map α (flip (ix-to-str {s = s})) var-names
      f ← num-step α var-names′ inp
      let body = showProgram f
      let args = intersperse "," $ toArgs s (num-map α just var-names)
      return $ printf "void %s(%s) {\n%s}\n" function-name args body

inp→f-Scl : (scl : Scalar τ) → Inp translate-Ty s (Scl scl) → String → String
inp→f-Scl {s = s} scl inp function-name = runState inp→f′ 0 .proj₂
  where
    inp→f′ : State ℕ String
    inp→f′ = do
      var-name′ ← fresh-var
      let var-name = var-name′
      f ← scl-step scl (flip ix-to-str var-name) inp
      let body = showProgram f
      return $ printf "void %s(%s) {\n%s}\n" function-name (ArCast (just var-name) (Scl-type scl) s) body 

inp-signature : (α : Num τ) → Inp translate-Ty s α → String → String
inp-signature {s = s} α inp function-name = printf "void %s(%s);\n" function-name (intersperse "," $ toArgs s (nothing-num-tuple α))

inp-signature-Scl : (scl : Scalar τ) → Inp translate-Ty s (Scl scl) → String → String
inp-signature-Scl {s = s} scl inp function-name = printf "void %s(%s);\n" function-name (ArCast nothing (Scl-type scl) s)

sizeDefs : (α : Num τ) → S ℓ → num-tuple String α → String
sizeDefs (Scl α) s name = (printf "#ifndef %s_SIZE\n" name)
                       ++ (printf "#define %s_SIZE %u\n" name (clen s))
                       ++ (printf "typedef %s (*%s_TYPE)%s;\n" (Scl-type α) name (ShapeCast s))
                       ++ "#endif\n"
sizeDefs (α₁ ⋆ α₂) s (xs , ys) = sizeDefs α₁ s xs ++ sizeDefs α₂ s ys

sizeDef-Complex : S ℓ → String → String
sizeDef-Complex s name =     (printf "#ifndef %s_SIZE\n" name)
                  ++ (printf "#define %s_SIZE %u\n" name (clen s))
                  ++ (printf "typedef complex real (*%s_TYPE)%s;\n" name (ShapeCast s))
                  ++ ("#define ARR_OF_COMPLEX\n")
                  ++ "#endif\n"
```

# Testing

```agda
module _ where

  fftn-test-sig-Complex′ : S (ss (ss zz)) → String
  fftn-test-sig-Complex′ s = inp-signature _ (fftn` s) "fftn"
                             -- inp-signature-Scl C (fftn` s) "fftn"

  fftn-test-sig′ : S (ss (ss zz)) → String
  fftn-test-sig′ s = inp-signature _ (Rfftn` s) "fftn"


  fftn-test-Complex′ : S (ss (ss zz)) → String
  fftn-test-Complex′ s =
    let fun = fftn` s in
    inp→f _ fun "fftn"
    --inp→f-Scl C fun "fftn"

  fftn-test′ : S (ss (ss zz)) → String
  fftn-test′ s =
    let fun = Rfftn` s in
    inp→f _ fun "fftn"
```
