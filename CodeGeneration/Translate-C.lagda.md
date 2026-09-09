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

open import Data.Nat
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String hiding (length)
open import Data.Product hiding (swap)
open import Data.Maybe renaming (_>>=_ to _⟫=_; zip to zipM) 
open import Data.Bool

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

  ix-to-str : Ix s → (String → String) → (String → String)
  ix-to-str i name pre = "(*" ++ name pre ++ ")" ++ (ix-to-subscripts i)

```

# Arithmetic Evaluator
We can then create an evaluator and translator for our Airthmetic operations.
Our evaluator is going to evaluate all lambda calculus, while the translator 
will stringify this into something which can be used in C. 

```agda
open import Data.List as List renaming (_++_ to _++ₗ_; [_] to [_]ₗ; map to mapₗ)
module _ where

  data NOp : Set where
    Nconst : ℕ → NOp
    Niota : Ix (ν n) → NOp
    Nmult : NOp → NOp → NOp
    
  data COp : Set where
    var : (String → String) → COp
    Cmult : COp → COp → COp
    ω : NOp → NOp → COp

  data AssignmentOperation : Set where
    ≔ : AssignmentOperation
    += : AssignmentOperation

  mutual
    data Instruction : Set where
      comment′ : String → Instruction
      assign′ : (String → String) → AssignmentOperation → COp → Instruction
      declare′ : (String → String) → S ℓ → Instruction
      loop′ : Ix s → Program → Instruction
      free′ : (String → String) → Instruction

    Program : Set
    Program = List Instruction


  data Val : Ty → Set where
    C : Val C
    N : Val N

  translate-Ty : (τ : Ty) → Set
  translate-Ty C = COp
  translate-Ty N = NOp
  translate-Ty (ix s) = Ix s
  translate-Ty (τ ⇒ τ₁) = translate-Ty τ → State ℕ (translate-Ty τ₁)

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
```

# C Helpers

We can then define a set of functions which spit out some common C strings for 
us. These lay out a structure for the eventual C dsl


```agda
module _ where
  real-type : String
  real-type = "real"

  complex-type : String
  complex-type = "complex" <+> real-type

  calloc-op : (type : String) → ℕ → String
  calloc-op ty s = printf "calloc(%u, sizeof(%s))" s ty

  for-template : String → ℕ → String → String
  for-template i n expr = printf "for (size_t %s = 0; %s < %u; %s++) {\n%s}\n" i i n i expr

  loopnest : Ix s → (String → String)
  loopnest {s = ν n} (ν i) = for-template i (suc n)
  loopnest (ι s) = loopnest s
  loopnest (s ⊗ s₁) = loopnest s ∘ loopnest s₁

  assignment : String → String → String
  assignment = printf "%s = %s;\n"

  +assignment : String → String → String
  +assignment = printf "%s += %s;\n"
  
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

  -- Placeholder ix
  β : Ix s 
  β {.zz} {ν x} = ν "β"
  β {.(ss _)} {ι s} = ι β
  β {.(ss _)} {s₁ ⊗ s₂} = β ⊗ β


  showIx : Ix s → String 
  showIx {.zz} {ν n} (ν i) = printf "%s < %u, " i (suc n)
  showIx {.(ss _)} {ι s} (ι i) = showIx i
  showIx {.(ss _)} {s ⊗ s₁} (i₁ ⊗ i₂) = showIx i₁ ++ showIx i₂

  calloc : String → S ℓ → State ℕ ((String → String) × Instruction × Instruction)
  calloc type s = do  
    memName′ ← fresh-var
    let memName = _++ memName′
    let ops = declare′ memName s
    let free = free′ memName
    return $ memName , ops , free
```

# C AST

If I create a small AST representing C, then migrating from ℂ to ℝ × ℝ should 
become trivial as we can make the change in the next translation step

```agda
module _ where
  evaled-to-str : Val τ → translate-Ty τ → String
  evaled-to-str C (var x) = x ""
  evaled-to-str C (Cmult op₁ op₂) = printf "(%s * %s)" (evaled-to-str C op₁) (evaled-to-str C op₂)
  evaled-to-str C (ω op₁ op₂) = printf "minus_omega(%s, %s)" (evaled-to-str N op₁) (evaled-to-str N op₂)
  evaled-to-str N (Nconst x) = showℕ x
  evaled-to-str N (Niota (ν i)) = i
  evaled-to-str N (Nmult op₁ op₂) = printf "(%s * %s)" (evaled-to-str N op₁) (evaled-to-str N op₂)

  showAssignmentOperation : AssignmentOperation → String
  showAssignmentOperation ≔ = "="
  showAssignmentOperation += = "+="

  showValue : COp → String
  showValue = evaled-to-str C

  --- THIS IS VERY CHEATY
  --{-# TERMINATING #-}
  --- This is less cheaty but not great either
  {-# NON_TERMINATING #-}
  mutual
    showInstruction : Instruction → String
    showInstruction (comment′ x) = unlines $ List.map ("//" <+>_) $ lines x
    showInstruction (assign′ var′ op′ val′) = (var′ "") <+> (showAssignmentOperation op′) <+> showValue val′
    showInstruction (loop′ i ins) = loopnest i (showProgram ins)
    showInstruction (free′ x) = printf "free(%s)" (x "")
    showInstruction (declare′ memName s) = printf "%s = %s" (ArCast (just (memName "")) complex-type s) (calloc-op "complex real" (clen s))

    showProgram  : Program → String
    showProgram = unlines ∘ List.map (_++ ";") ∘ List.map showInstruction 

module _ where

  evil : String
  evil = "knievel"

  data Component : Set where
    re : Component
    im : Component

  --evaled-to-str₂ : Component → Val τ → translate-Ty τ → String
  --evaled-to-str₂ = ?

  showNOp₂ : NOp → String
  showNOp₂ (Nconst n) = showℕ n
  showNOp₂ (Niota (ν i)) = i
  showNOp₂ (Nmult op₁ op₂) = printf "(%s * %s)" (showNOp₂ op₁) (showNOp₂ op₂)

  prefix-string : Component → String → String
  prefix-string re = printf "r_%s"
  prefix-string im = printf "i_%s"

  prefix-var : Component → (String → String) → String
  prefix-var re f = f "r_"
  prefix-var im f = f "i_"
    
  showCOp₂ : Component → COp → String
  showCOp₂ component (var x) = prefix-var component x
  showCOp₂ re (Cmult op₁ op₂) =
    let
      a = showCOp₂ re op₁
      b = showCOp₂ im op₁
      c = showCOp₂ re op₂
      d = showCOp₂ im op₂
      in printf "((%s * %s) - (%s * %s))" a c b d
  showCOp₂ im (Cmult op₁ op₂) =
    let
      a = showCOp₂ re op₁
      b = showCOp₂ im op₁
      c = showCOp₂ re op₂
      d = showCOp₂ im op₂
      in printf "((%s * %s) + (%s * %s))" a d b c
  showCOp₂ component (ω op₁ op₂) = prefix-string component (printf "minus_omega(%s, %s)" (evaled-to-str N op₁) (evaled-to-str N op₂))

  {-# NON_TERMINATING #-}
  mutual
    showInstruction₂ : Instruction → List String
    showInstruction₂ (comment′ x) = [ unlines $ List.map ("//" <+>_) $ lines x ]ₗ
    showInstruction₂ (assign′ var′ op′ val′) = let
      inst₁ = evil                 <+> "=" <+> showCOp₂ re val′
      inst₂ = (prefix-var im var′) <+> (showAssignmentOperation op′) <+> showCOp₂ im val′
      inst₃ = (prefix-var re var′) <+> (showAssignmentOperation op′) <+> evil
      in inst₁ ∷ inst₂ ∷ [ inst₃ ]ₗ
      --inst = λ comp → (prefix-var comp var′) <+> (showAssignmentOperation op′) <+> showCOp₂ comp val′
      -- in mapₗ inst $ re ∷ [ im ]ₗ
    showInstruction₂ (declare′ var′ s) = let
      inst = λ comp → printf "%s = %s" (ArCast (just (prefix-var comp var′)) real-type s) (calloc-op real-type (clen s))
      in mapₗ inst $ re ∷ [ im ]ₗ
    showInstruction₂ (loop′ i prog) = [ loopnest i (showProgram₂ prog) ]ₗ
    showInstruction₂ (free′ var′) = let
      inst = λ comp → printf "free(%s)" $ prefix-var comp var′
      in mapₗ inst $ re ∷ [ im ]ₗ

    showProgram₂  : Program → String
    showProgram₂ = unlines ∘ List.map (_++ ";") ∘ List.concatMap showInstruction₂
```


# C Translation

Finally we can move to our C translation

```agda
step₁ : (Ix s → (String → String)) → Inp translate-Ty s → (State ℕ Program)
step₁ ar (imap` arit) = do
  i ← new-Ix _
  arit′ ← arit-eval (app (app arit (var i)) (var (var (ar i))))
  return $ [ loop′ i [ assign′ (ar i) ≔ arit′ ]ₗ ]ₗ
step₁ xs (compose inp₁ inp₂) = do
  ins₁ ← step₁ xs inp₁ 
  ins₂ ← step₁ xs inp₂
  return $ ins₁ ++ₗ ins₂
step₁ xs (mapSum` {u} arit) = do
  memName , assign , free ← calloc complex-type (ι (ν u))

  i ← new-Ix (ι (ν u))
  j ← new-Ix (ι (ν u))
  k ← new-Ix (ι (ν u))

  op ← arit-eval $ app (app (app arit (`λ l ⇒ (var (var (xs l))))) (var i)) (var j)

  let body = loop′ j [ loop′ i [ assign′ (ix-to-str i memName) += op ]ₗ ]ₗ

  let copyBack = loop′ k [ assign′ (xs k) ≔ (var (ix-to-str k memName)) ]ₗ
  return $ assign ∷ body ∷ copyBack ∷ [ free ]ₗ
step₁ xs (copyOut` {_} {s} {p} r₁ r₃ inp) = do 
  workingMem , assign , free ← calloc complex-type p

  i ← new-Ix s
  let copyOutOp = comment′ (showResh r₁)
                ∷ [ loop′ i [ assign′ (ix-to-str (resh-ix r₁ i) workingMem) ≔ (var (xs (ι i))) ]ₗ ]ₗ

  op ← step₁ (flip ix-to-str workingMem) inp

  j ← new-Ix s
  let copyInOp = comment′ (showResh r₃)
              ∷ [ loop′ j [ assign′ (xs (ι j)) ≔ (var (ix-to-str (resh-ix (rev r₃) j) workingMem)) ]ₗ ]ₗ

  return $ [ assign ]ₗ ++ₗ copyOutOp ++ₗ op ++ₗ copyInOp ++ₗ [ free ]ₗ
step₁ xs (part` {_} {s} {p} s⊂p inp) = do
  i ← new-Ix s
  let ys = λ j → xs (resh-ix (rev (to-resh s⊂p)) (i ⊗ j))

  op ← step₁ ys inp

  return $ [ loop′ i op ]ₗ

inp→f-Complex : Inp translate-Ty s → String → String
inp→f-Complex {_} {s} inp function-name = runState inp→f′ 0 .proj₂
  where
    inp→f′ : State ℕ String
    inp→f′ = do
      var-name′ ← fresh-var
      let var-name = _++ var-name′
      f ← step₁ (flip ix-to-str var-name) inp
      let body = showProgram f
      return $ printf "void %s(%s) {\n%s}\n" function-name (ArCast (just (var-name "")) complex-type s) body 

inp→f-Real : Inp translate-Ty s → String → String
inp→f-Real {_} {s} inp function-name = runState inp→f′ 0 .proj₂
  where
    inp→f′ : State ℕ String
    inp→f′ = do
      var-name′ ← fresh-var
      let var-name = _++ var-name′
      f ← step₁ (flip ix-to-str var-name) inp
      let body = showProgram₂ f
      let assignEvil = printf "real %s = 0;" evil
      return $ printf "void %s(%s, %s) {\n%s\n%s}\n" 
          function-name 
          (ArCast (just (prefix-var re var-name)) real-type s) 
          (ArCast (just (prefix-var im var-name)) real-type s) 
          assignEvil
          body 

inp-signature-Complex : Inp translate-Ty s → String → String
inp-signature-Complex {_} {s} inp function-name = printf "void %s(%s);\n" function-name (ArCast nothing complex-type s)

inp-signature-Real : Inp translate-Ty s → String → String
inp-signature-Real {_} {s} inp function-name = printf "void %s(%s, %s);\n" function-name (ArCast nothing real-type s) (ArCast nothing real-type s)

sizeDef-Complex : S ℓ → String → String
sizeDef-Complex s name =     (printf "#ifndef %s_SIZE\n" name)
                  ++ (printf "#define %s_SIZE %u\n" name (clen s))
                  ++ (printf "typedef complex real (*%s_TYPE)%s;\n" name (ShapeCast s))
                  ++ ("#define ARR_OF_COMPLEX\n")
                  ++ "#endif\n"

sizeDef-Real : S ℓ → String → String
sizeDef-Real s name =     (printf "#ifndef %s_SIZE\n" name)
                  ++ (printf "#define %s_SIZE %u\n" name (clen s))
                  ++ (printf "typedef real (*%s_TYPE)%s;\n" name (ShapeCast s))
                  ++ "#endif\n"
```

# Testing

```agda
module _ where

  fftn-test-sig-Complex′ : S (ss (ss zz)) → String
  fftn-test-sig-Complex′ s = inp-signature-Complex (fftn` s) "fftn"

  fftn-test-sig-Real′ : S (ss (ss zz)) → String
  fftn-test-sig-Real′ s = inp-signature-Real (fftn` s) "fftn"


  fftn-test-Complex′ : S (ss (ss zz)) → String
  fftn-test-Complex′ s =
    let fun = fftn` s in
    inp→f-Complex fun "fftn"

  fftn-test-Real′ : S (ss (ss zz)) → String
  fftn-test-Real′ s =
    let fun = fftn` s in
    inp→f-Real fun "fftn"
```
