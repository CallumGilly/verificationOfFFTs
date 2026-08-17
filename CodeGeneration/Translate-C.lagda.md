Here I define the translation from the DSL into C...
```agda

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
open import Data.Product
open import Data.Maybe hiding (_>>=_)
open import Data.Bool

open import Relation.Binary.PropositionalEquality

open import Text.Printf

open import CodeGeneration.DSL

private variable
  τ σ : Ty
  l : L
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

I then define how each type will be represented within C.

To represent indices I need to create a representation of indexes where each 
leaf of the shape tree is a variable (or stringified operation).

```agda
data Ix : S l → Set where
  ν : ∀ {n : ℕ} → String → Ix (ν n)
  ι : ∀ {s : S l} → Ix s → Ix (ι s)
  _⊗_ : ∀ {s p : S (ss l)} → Ix s → Ix p → Ix (s ⊗ p)

-- Split translate-inp such that we eval and then to-string such that we can compose 
translate-Ty : Ty → Set
translate-Ty C = String
translate-Ty N = String
translate-Ty (ix s) = Ix s
translate-Ty (τ ⇒ σ) = translate-Ty τ → State ℕ (translate-Ty σ)
```

For this Ix type I create a function to make an Ix instance where every leaf 
is a new variable (for use when generating loop nests).
```agda
new-Ix : ∀ {l : L} (s : S l) → State ℕ (Ix s)
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

```agda
clen : S l → ℕ
clen = suc ∘ length
```

We also need a way to reshape IX then get the flat position.
We can also then create a function to get this position after a reshape has been applied
```agda
ix-flat-index : ∀ {s : S l} → Ix s → String
ix-flat-index (ν i) = i
ix-flat-index (ι i) = ix-flat-index i
ix-flat-index (_⊗_ {s = s} {p} i j) = parensIfSpace $ (ix-flat-index i) <+> "+" <+> parensIfSpace ((showℕ $ length s) <+> "*" <+> ix-flat-index j)

ix-resh-flat-index : ∀ {l l′ : L} {s : S l} {p : S l′} → Ix s → Reshape p s → String
ix-resh-flat-index i eq = ix-flat-index i
ix-resh-flat-index i (r ∙ r₁) = "TODO: Resh" -- This is an interesting case which may trip me up
ix-resh-flat-index i (r ⊕ r₁) = "TODO: Resh"
ix-resh-flat-index i (up r) = "TODO: Resh"
ix-resh-flat-index i (down r) = "TODO: Resh"
ix-resh-flat-index i flat = "TODO: Resh"
ix-resh-flat-index i unflat = "TODO: Resh"
ix-resh-flat-index i swap = "TODO: Resh"
ix-resh-flat-index i assoₗ = "TODO: Resh"
ix-resh-flat-index i assoᵣ = "TODO: Resh"
```

We can then create an evaluator and translator for our Airthmetic operations.
Our evaluator is going to evaluate all lambda calculus, while the translator 
will stringify this into something which can be used in C. 

```agda
arit-eval : ∀ {τ : Ty} → Arit translate-Ty τ → State ℕ (translate-Ty τ)
arit-eval (var x) = return x
arit-eval (lam x) = return (arit-eval ∘ x)
arit-eval (app f x) = do
  f′ ← arit-eval f
  x′ ← arit-eval x
  f′ x′
arit-eval (sizeN {s = s} x) =
  return $ printf "%u" $ clen s
arit-eval (posiN i r) = do
  i′ ← arit-eval i
  return $ ix-resh-flat-index i′ r
arit-eval (spliₗ x) = do
  (i ⊗ _) ← arit-eval x
  return i
arit-eval (spliᵣ x) = do
  (_ ⊗ i) ← arit-eval x
  return i
arit-eval (x *N y) = do
  x′ ← arit-eval x
  y′ ← arit-eval y
  return $ parens $ x′ <+> "*" <+> y′
arit-eval (x *C y) = do
  x′ ← arit-eval x
  y′ ← arit-eval y
  return $ parens $ x′ <+> "*" <+> y′
arit-eval (ω` x y) = do
  x′ ← arit-eval x
  y′ ← arit-eval y
  return $ parens $ "omega(" ++ x′ ++ "," <+> y′ ++ ")"
```

We can then create a function which takes this evaluated form into string form.
This feels wrong however, as the array case is blatantly useless.......
```agda
evaled-to-str : Num τ → translate-Ty τ → State ℕ String
evaled-to-str (C) x = return x
evaled-to-str (N) x = return x
evaled-to-str ((arr {s = s} num-τ)) xs = do
  i ← new-Ix s
  x ← xs i
  evaled-to-str (num-τ) x

translate-Arit : Num τ → Arit translate-Ty τ → State ℕ String
translate-Arit a b = evaled-to-str a =<< arit-eval b
```

One curiosity here is that the sizeN case needs the successor of length, this 
is suspicious to me and hints that there MAY be an issue with my implementation 
of `natMon` (where `U = Fin ∘ suc`)
```agda

module Arit-Test where
  Test-complexMult : Arit translate-Ty C 
  Test-complexMult = ((var "VarA") *C (var "VarB"))
  
  Test-size₁ : Arit translate-Ty N
  Test-size₁ = sizeN (var (ι (ν {2} "VarA")))

  Test-size₂ : Arit translate-Ty N
  Test-size₂ = sizeN (var (ι (ν {4} "VarA") ⊗ ι (ν {3} "VarB")))

  Test-lambda : Arit translate-Ty N
  Test-lambda = app ( `λ x ⇒ (var x) *N (var "VarA") ) (var {translate-Ty} {N} "VarB")

{-
open Arit-Test
entry : String
entry = (runState (translate-Arit (num N) Test-size₂) 0) .proj₂
-}

```

# Sel
Sel (selector) allows for an index to be partially given. The first
argument of Sel is the shape of the remainder, while the second is the overall 
shape which the remainder can be found within.

Not quite sure how I want to define sel given the two levels.
One option is to restrict it to only work on one level
But this will definitly end up too restrictive
```agda
data Sel : ∀ {l₁ l₂ : L} → S l₁ → S l₂ → Set where
  idh : ∀ {l : L} {s : S l} → Sel s s
  left : ∀ {l : L} {s p₁ p₂ : S (ss l)} → Ix p₂ → Sel s p₁ → Sel s (p₁ ⊗ p₂)
  right : ∀ {l : L} {s p₁ p₂ : S (ss l)} → Ix p₁ → Sel s p₂ → Sel s (p₁ ⊗ p₂)
  both  : ∀ {l : L} {s₁ s₂ p₁ p₂ : S (ss l)} → Sel s₁ p₁ → Sel s₂ p₂ → Sel (s₁ ⊗ s₂) (p₁ ⊗ p₂)
  chain : ∀ {l₁ l₂ l₃ : L} {s₁ : S l₁} {s₂ : S l₂} {s₃ : S l₃}  → Sel s₁ s₂ → Sel s₂ s₃ → Sel s₁ s₃
```

As well as sel, I need a way to translate from subshape to sel. 
This takes a shape p, and a shape within it s, and returns a new iterator for 
the inner shape `s`, and a selector into the remainder of the shape
```agda
⊂-to-sel : ∀ {l : L} {s : S l} {p : S l} → (s⊂p : s ⊂ p) → State ℕ (Ix s × Sel (inv-⊂ s⊂p) p)
⊂-to-sel {s = s} (le {s₂ = p} id) = do
  ix-s ← new-Ix s
  return $ ix-s , right ix-s idh
⊂-to-sel {s = s} (le {s₁ = p₁} {p₂} (st s⊂p₁)) = do
  ix-s , sel ← ⊂-to-sel s⊂p₁
  return $ ix-s , both sel idh
⊂-to-sel {s = s} (ri id) = do
  ix-s ← new-Ix s
  return $ ix-s , left ix-s idh
⊂-to-sel {s = s} (ri {s₁ = p₁} {p₂} (st s⊂p₂)) = do
  ix-s , sel ← ⊂-to-sel s⊂p₂ 
  return $ ix-s , both idh sel
⊂-to-sel {s = .(q₁ ⊗ q₂)} (bₗ {q₁ = q₁} {q₂} {s₁} {.q₂} q₁⊂s₁ id) = do 
  ix-q₁ , sel ← ⊂-to-sel q₁⊂s₁
  ix-q₂ ← new-Ix q₂
  return $ ix-q₁ ⊗ ix-q₂ , left ix-q₂ sel 
⊂-to-sel {s = .(q₁ ⊗ q₂)} (bₗ {q₁ = q₁} {q₂} {s₁} {s₂} q₁⊂s₁ (st q₂⊂s₂)) = do
  ix-q₁ , sel₁ ← ⊂-to-sel q₁⊂s₁
  ix-q₂ , sel₂ ← ⊂-to-sel q₂⊂s₂
  return $ ix-q₁ ⊗ ix-q₂ , both sel₁ sel₂
⊂-to-sel {s = .(q₁ ⊗ q₂)} (bᵣ {q₁ = q₁} {q₂} {.q₁} {s₂} id q₂⊂s₂) = do
  ix-q₁ ← new-Ix q₁
  ix-q₂ , sel ← ⊂-to-sel q₂⊂s₂
  return $ ix-q₁ ⊗ ix-q₂ , right ix-q₁ sel
⊂-to-sel {s = .(q₁ ⊗ q₂)} (bᵣ {q₁ = q₁} {q₂} {s₁} {s₂} (st q₁⊂s₁) q₂⊂s₂) = do
  ix-q₁ , sel₁ ← ⊂-to-sel q₁⊂s₁
  ix-q₂ , sel₂ ← ⊂-to-sel q₂⊂s₂
  return $ ix-q₁ ⊗ ix-q₂ , both sel₁ sel₂
```

If we are given an Ix into the remainder we can convert a selector to Ix
```agda
sel-to-ix : ∀ {l l′} {s : S l} {s′ : S l′} → Sel s s′ → Ix s → Ix s′
sel-to-ix idh i = i
sel-to-ix (left x sel) i = sel-to-ix sel i ⊗ x
sel-to-ix (right x sel) i = x ⊗ sel-to-ix sel i
sel-to-ix (both selₗ selᵣ) (iₗ ⊗ iᵣ) = sel-to-ix selₗ iₗ ⊗ sel-to-ix selᵣ iᵣ
sel-to-ix (chain sel₁ sel₂) i = sel-to-ix sel₂ (sel-to-ix sel₁ i)
```

We then create a converter from ix to subscripts to allow us to stringify them.
```agda
ix-to-subscripts : ∀ {s : S l} → Ix s → String
ix-to-subscripts (ν i) = "[" ++ i ++ "]"
ix-to-subscripts (ι i) = ix-to-subscripts i
ix-to-subscripts (i ⊗ j) = ix-to-subscripts i ++ ix-to-subscripts j
```

# C Helpers

We can then define a set of functions which spit out some common C strings for 
us. These lay out a structure for the eventual C dsl


```agda
data DefEq : Set where
  ≕  : DefEq
  += : DefEq

data Var : Set where
  Jst : String → Var

data Val : Set where

data Instruction : Set where
  initialisation : Instruction
  Assignment : Var → DefEq → Val → Instruction

data Program : Set where
  iterator : ∀ {s : S l} → Ix s → Program → Program
  instruction : Instruction → Program
  _∺_ : Program → Program → Program

ix-to-str : ∀ {s : S l} → Ix s → String → String
ix-to-str i name = name ++ (ix-to-subscripts i)

sel-to-str : ∀ {l l′ : L} {s : S l} {s′ : S l′} → Sel s s′ → String → (Ix s → State ℕ String)
sel-to-str sel name i = return $ ix-to-str (sel-to-ix sel i) name

real-type : String
real-type = "real"

complex-type : String
complex-type = "complex" <+> real-type

malloc-op : (type : String) → ℕ → String
malloc-op ty s = printf "malloc(%u * sizeof(%s))" s ty
--
calloc-op : (type : String) → ℕ → String
calloc-op ty s = printf "calloc(%u, sizeof(%s))" s ty

free-op : String → String
free-op = printf "free(%s)"

for-template : String → ℕ → String → String
for-template i n expr = printf "for (size_t %s = 0; %s < %u; %s++) {\n%s}\n" i i n i expr

loopnest : ∀ {l : L} {s : S l} → Ix s → (String → String)
loopnest {s = ν n} (ν i) = for-template i (suc n)
loopnest (ι s) = loopnest s
loopnest (s ⊗ s₁) = loopnest s ∘ loopnest s₁

assignment : String → String → String
assignment = printf "%s = %s;"

+assignment : String → String → String
+assignment = printf "%s += %s;"

_>:_ : String → String → String
_>:_ = printf "%s;\n%s"
_>∷_ : String → String → String
_>∷_ = printf "%s\n%s"
infixl 6 _>:_
infixl 6 _>∷_

 {-
show-Instruction : Instruction → String

show-Program : Program → String
show-Program (iterator i p) = loopnest i (show-Program p)
show-Program (instruction x) = show-Instruction x
show-Program (x ∺ y) = show-Program x ++ ";\n" ++ show-Program y
-}
```

We can then create a small helper which allows us to create and then free 
memory - eventually it may be nice to consider making this reuse the "Scratch"
memory such that we are not constantly allocing and freeing
```
-- Create
{-
cplx-memory-lifetime : S zz → (String → String) → State ℕ String
cplx-memory-lifetime (ν n) f = do
  memory-name ← fresh-var
  -- May need to add def
  let memory-alloc = assignment (complex-type <+> "*" ++ memory-name) $ "(" ++ complex-type <+> "*)" ++ calloc-op complex-type n
  let ops = f memory-name 
  let memory-free = free-op memory-name
  return $ memory-alloc >: ops >: memory-free
-}
```
# C Translation

Finally we can move to our C translation, this works in two steps. 
- translateInp₁ 

Here we define the subset of Ty containing arrays only, together with a name. 
This is the set of things we can operate over inplace.
```agda
data AR : Ty → Set where
  arr : ∀ {l₁ l₂ : L} {s : S l₁} {p : S l₂} {τ : Ty} → String → Sel p s → AR (ar p τ)
```

I had the thought of creating a small dsl for pointer arithmetic to make it 
harder to cock up, but I think I'm being a bit thick atm trying to convert ix 
to a pointer representation
```agda


placeholder-Ix : (s : S l) → Ix s
placeholder-Ix (ν x) = ν "PLACEHOLDER-IX"
placeholder-Ix (ι s) = ι (placeholder-Ix s)
placeholder-Ix (s ⊗ s₁) = placeholder-Ix s ⊗ placeholder-Ix s₁

resh-ix : ∀ {l l′ : L} {s : S l} {s′ : S l′} → Reshape s s′ → Ix s → Ix s′
resh-ix eq i = i
resh-ix (r ∙ r₁) i = resh-ix r (resh-ix r₁ i)
resh-ix (r ⊕ r₁) (i ⊗ j) = resh-ix r i ⊗ resh-ix r₁ j
resh-ix (up r) i = ι (resh-ix r i)
resh-ix (down r) (ι i) = resh-ix r i
resh-ix swap (i ⊗ j) = j ⊗ i
resh-ix assoₗ ((i₁ ⊗ i₂) ⊗ i₃) = i₁ ⊗ (i₂ ⊗ i₃)
resh-ix assoᵣ (i₁ ⊗ (i₂ ⊗ i₃)) = (i₁ ⊗ i₂) ⊗ i₃
-- These need mod, just needs a moment of thinking
resh-ix (flat {m} {n}) (ι (ν b) ⊗ ι (ν b₁)) = ν (printf "((%u * %s) + %s)" m b b₁) --placeholder-Ix _
resh-ix (unflat {m} {n}) (ν x) = ι (ν (printf "(%s / %u)" x m )) ⊗ ι (ν (printf "(%s %% %u)" x m)) --placeholder-Ix _

--resh-ix-pointer : ∀ {s s′ : S l} → Reshape s s′ → Ix s → Pointer (length s′)
--resh-ix-pointer r i = ix-pointer (resh-ix r i)
```
# New Attempts

```agda
module _ where
  variable 
    ℓ ℓ′ : L
    s s′ k : S ℓ
    r : Reshape s s′



  ShapeCast : S ℓ → String
  ShapeCast = ShapeCast′ true
    where
      ShapeCast′ : Bool → S ℓ → String
      ShapeCast′ isLeft (ι s) = ShapeCast′ isLeft s
      ShapeCast′ isLeft (s₁ ⊗ s₂) = ShapeCast′ isLeft s₁ ++ ShapeCast′ false s₂
      ShapeCast′ false (ν x) = printf "[%u]" (suc x)
      ShapeCast′ true (ν x) = ""

  ArCast : Maybe String → S ℓ → String
  ArCast nothing = parens ∘ ArCast (just "")
  ArCast (just memName) = printf "%s (*%s)%s" complex-type memName ∘ ShapeCast

  commentBlock : String → String → String
  commentBlock comment body = printf "//Start: %s\n%s//End: %s\n" comment body comment

  calloc : String → S ℓ → State ℕ (String × String)
  calloc type s = do  
    memName ← fresh-var
    let ops = assignment (ArCast (just memName) s) $ (ArCast nothing s) ++ (calloc-op type (clen s))
    return $ memName , ops

  step₁ : .( r : Reshape s s′ ) → (Ix s → String) {-AR′ s-} → Inp translate-Ty s s′ r → (Ix s′ → String) × (State ℕ String)
  step₁ _ ar (imap` arit) = ar , operation
    where
      operation = do
        i ← new-Ix _
        arit-string ← translate-Arit C (app (app arit (var i)) (var (ar i)))
        return $ commentBlock "imap" $ loopnest i (assignment (ar i) arit-string)
  step₁ _ xs (compose r₁ inp₁ r₂ inp₂) = op₂ .proj₁ , ops
    where
      op₁ = step₁ r₁ xs inp₁
      op₂ = step₁ r₂ (op₁ .proj₁) inp₂
      ops = do
        ins₁ ← op₁ .proj₂
        ins₂ ← op₂ .proj₂
        return $ commentBlock "compose" $ ins₁ ++ "//Middle: compose\n" ++ ins₂
  step₁ _ xs (mapSum` {u} arit) = xs , ops
    where
      ops = do
        memName , assign ← calloc complex-type (ι (ν u))

        i ← new-Ix (ι (ν u))
        j ← new-Ix (ι (ν u))
        k ← new-Ix (ι (ν u))

        op ← translate-Arit C $ app (app (app arit (`λ l ⇒ (var (xs l)))) (var i)) (var j)
        let body = loopnest j $ loopnest i $ +assignment (ix-to-str i memName) op

        let copyBack = loopnest k $ assignment (xs k) (ix-to-str k memName)
        
        return $ commentBlock "mapSum" $ assign ++ body ++ copyBack
  step₁ _ xs (copyOut` {_} {s} {s′} {p} {q} r₁ r₂ r₃ inp) = zs , ops
    where
      zs = xs ∘ resh-ix (up (down (rev (r₃ ∙ r₂ ∙ r₁))))
      ops = do
        memName₁ , assign ← calloc complex-type p

        i ← new-Ix p
        let out-op = printf "%s = %s;\n" (ix-to-str i memName₁) (xs (resh-ix (up (rev r₁)) i))
        let out = (loopnest i out-op) ++ "\n"

        let ys , op-f = step₁ r₂ (flip ix-to-str memName₁) inp
        op ← op-f
        
        memName₂ ← fresh-var
        let re-cast = assignment (ArCast (just memName₂) s′) (ArCast nothing s′ <+> memName₁)

        j ← new-Ix s′
        let inn-op = assignment (zs (resh-ix (up eq) j)) (ix-to-str j memName₂)
        let inn = (loopnest j inn-op) ++ "\n"

        return $ commentBlock "copyOut" $ assign ++ out ++ op ++ re-cast ++ inn
  step₁ _ xs (part` {_} {s} {p} s⊂p inp) = xs , ops
    where
      ops = do
        i ← new-Ix s
        let ys = λ j → xs (resh-ix (rev (to-resh s⊂p)) (i ⊗ j))

        let _ , op-f = step₁ eq ys inp
        op ← op-f

        return $ commentBlock "part" $ loopnest i op

  show-inp : Inp translate-Ty s s′ r → String
  show-inp {_} {_} {_} {r} inp = runState show-inp′ 0 .proj₂ 
     where
       show-inp′ : State ℕ String
       show-inp′ = do 
         let _ , f = step₁ r (flip ix-to-str "memName") inp
         x ← f
         return $ x

  funk : ∀ {s p : S l} → Reshape s p → Reshape (ι s) (ι p)
  funk r = up (down r)

  -- Takes an array, doubles every value and transposes the result
  mini₁ : ∀ {s : S (ss ℓ)} → Inp translate-Ty (ι s) (ι (transp s)) (funk (rev transpᵣ))
  mini₁ {_} {s} = copyOut` {_} {_} {s} {transp s} {s} {s} eq eq (rev transpᵣ) (imap` (`λ i ⇒ `λ x ⇒ var x *C var "2"))

  mini₂ : ∀ {s : S (ss ℓ)} → Inp translate-Ty (ι s) (ι (transp s)) (funk (rev transpᵣ))
  mini₂ {_} {s} = compose (funk (rev transpᵣ)) mini₁ eq (imap` (`λ i ⇒ `λ x ⇒ var x))

  mini₃ : ∀ {s : S zz} → Inp translate-Ty (ι s) (ι s) eq
  mini₃ {ν u} = mapSum` (`λ x ⇒ `λ i ⇒ var x)

  mini₄ : Inp translate-Ty (ι (ν 3) ⊗ ι (ν 5)) _ eq
  mini₄ = part` (ri _⊆_.id) (imap` (`λ i ⇒ `λ x ⇒ var x *C (ω` (sizeN (var i)) (posiN (var i) eq))))
```

# Main Attempt

```agda
--translateInp′ : {s s′ : S l} .{r : Reshape s s′} → AR (ix s ⇒ C) → Ix s → Inp translate-Ty s s′ r → State ℕ (AR (ix s′ ⇒ C) × translate-Ty C)
{-
translateInp₁′ : {s s′ : S l} .{r : Reshape s s′} → AR (ix s ⇒ C) → Ix s → Inp translate-Ty s s′ r → State ℕ (AR (ix s′ ⇒ C) × translate-Ty C)
translateInp₁′ ar@(arr ref sel) i (compose a inp₁ b inp₂) = do 
  ar₁ , e₁ ← translateInp₁′ ar i inp₁
  ar₂ , e₂ ← translateInp₁′ ar₁ (resh-ix a i) inp₂
  return $ ar₂ , (e₁ <+> "\n" <+> e₂)
-- translateInp₁′ (arr ref sel) i (view` r) = return $ (arr ref idh) , "" --TODO
translateInp₁′ tmp@(arr ref sel) i (copyOut` {s = s} {p} {q} r₁ r₂ inp) = do 
  let comment₁ = "//copyOut` Start"

  memory-name ← fresh-var
  let memory-alloc = assignment (complex-type <+> "*" ++ memory-name) $ "(" ++ complex-type <+> "*)" ++ calloc-op complex-type (suc (length s))

  copy-out-iter ← new-Ix s
  let copy-out-op = loopnest copy-out-iter $ assignment (ix-to-str (resh-ix r₁ copy-out-iter) memory-name) (ix-to-str (sel-to-ix sel (ι copy-out-iter)) ref)

  -- TODO
  iter ← new-Ix p
  some , inner ← translateInp₁′ (arr memory-name idh) iter inp

  copy-in-iter ← new-Ix q
  let copy-in-op  = loopnest copy-in-iter $ assignment (ix-to-str (sel-to-ix sel (resh-ix (up r₂) copy-in-iter) ) ref) (ix-to-str copy-in-iter memory-name)

  let comment₂ = "//copyOut` End\n"

  return (tmp , comment₁ >∷ memory-alloc >: copy-out-op >∷ inner >∷ copy-in-op >∷ comment₂)
translateInp₁′ ar@(arr ref sel) i (part` p⊂s inp) = do
  -- First we create a selection into the section of the array we want to work 
  -- with, with an iterator for the outer loop
  iter , inner-sel ← ⊂-to-sel p⊂s
  -- Then we generate the body of the loop, using that selection into the array
  tmp-iter ← new-Ix (inv-⊂ p⊂s)
  _ , inner ← translateInp₁′ (arr ref (chain inner-sel sel)) tmp-iter inp
  return $ ar , (loopnest iter $ loopnest tmp-iter inner) 

translateInp₁′ ar@(arr {s = s} {p} ref sel) i (imap` arit) = do
  ix-p ← new-Ix p

  current-x ← sel-to-str sel ref ix-p
  arit-string ← translate-Arit C (app (app arit (var ix-p)) (var current-x))
  return $ ar , (loopnest ix-p (current-x <+> "=" <+> arit-string ++ ";"))
translateInp₁′ ar@(arr ref sel) i (mapSum` {u} arit) = do
  -- For sum I need to allocate some memory to work in, this should be the 
  -- same size and shape of s
  iter₁ ← new-Ix _
  iter₂ ← new-Ix _
  airt ← translate-Arit (arr C) (app (app arit (var (sel-to-str sel ref))) (var iter₁))
  let f = λ tmp-name → ((loopnest iter₁ $ (ix-to-str iter₁ tmp-name) <+> "+=" <+> airt) >: (loopnest iter₂ $ assignment (ix-to-str (sel-to-ix sel iter₂) ref) (ix-to-str iter₂ tmp-name <+> ";\n")))
  lifetime ← cplx-memory-lifetime (ν u) f
  return $ ar , lifetime --(lifetime , loc)

translateInp₂ : ∀ {s s′ : S l} .(r : Reshape s s′) → AR (ix s ⇒ C) → Inp translate-Ty s s′ r → String  → String × String
translateInp₂ {s = s} _ ARτ inp name = runState (
        do
            iter ← new-Ix s
            _ , code ← translateInp₁′ ARτ iter inp
            return $ "" , loopnest iter code
      ) 0 .proj₂
      -}
{-
translateInp₁′ x i (compose x₁ x₂) = do
  a ← translateInp₁′ ? i ?
  return ?
translateInp₁′ x i (view` r) = ?
translateInp₁′ x i (copyOut` x₁ x₂ x₃) = ?
translateInp₁′ x i (part` s⊂p x₁) = ?
translateInp₁′ x i (imap` x₁) = ?
translateInp₁′ x i (mapSum` x₁) = ?


translateInp₁ : ∀ {ITy OTy : Ty} → FNum ITy → AR ITy → Inp translate-Ty ITy OTy → State ℕ (String × AR OTy)
-- This could probably be generalised
translateInp₁ fnum loc (compose inp₁ {a} inp₂ {b}) rewrite memCompatible a = do
  a , a′ ← translateInp₁ fnum loc inp₁
  b , b′ ← translateInp₁ fnum a′ inp₂
  return (a <+> "\n" <+> b , b′ )
translateInp₁ _ loc (view` r) = return ("TODO2" , arr "TODO" idh)
-- This is the point at which we are dealing with Levels
translateInp₁ (num (arr numτ)) loc@(arr name sel) (copyOut` {l} {_} {s} {q = q} r₁ r₂ inp) = do 
  let comment₁ = "//copyOut` Start"

  memory-name ← fresh-var
  let memory-alloc = assignment (complex-type <+> "*" ++ memory-name) $ "(" ++ complex-type <+> "*)" ++ calloc-op complex-type (suc (length s))

  copy-out-iter ← new-Ix s
  let copy-out-op = loopnest copy-out-iter $ assignment (ix-to-str (resh-ix r₁ copy-out-iter) memory-name) (ix-to-str (sel-to-ix sel (ι copy-out-iter)) name)

  inner , _ ← translateInp₁ (num (arr numτ)) (arr memory-name idh) inp

  copy-in-iter ← new-Ix q
  let copy-in-op  = loopnest copy-in-iter $ assignment (ix-to-str (sel-to-ix sel (resh-ix (up r₂) copy-in-iter) ) name) (ix-to-str copy-in-iter memory-name)

  let comment₂ = "//copyOut` End\n"

  return (comment₁ >∷ memory-alloc >: copy-out-op >∷ inner >∷ copy-in-op >∷ comment₂ , loc)

translateInp₁ (num (arr {s = s} numτ)) loc@(arr {s = c} name outer-sel) (part` {s = p} p⊂s inp) = do
  -- First we create a selection into the section of the array we want to work 
  -- with, with an iterator for the outer loop
  iter , inner-sel ← ⊂-to-sel p⊂s
  -- Then we generate the body of the loop, using that selection into the array
  inner , _ ← translateInp₁ (num (arr numτ)) (arr name (chain inner-sel outer-sel)) inp
  return ((loopnest iter inner) , loc)

translateInp₁ _ loc@(arr {p = p} name outer-sel) (imap` arit) = do
  ix-p ← new-Ix p

  current-x ← sel-to-str outer-sel name ix-p
  arit-string ← translate-Arit C (app (app arit (var ix-p)) (var current-x))
  return (loopnest ix-p (current-x <+> "=" <+> arit-string ++ ";") , loc)

translateInp₁ (num (arr C)) loc@(arr {s = s} name sel) (mapSum` {u} arit) = do 
  -- For sum I need to allocate some memory to work in, this should be the 
  -- same size and shape of s
  iter₁ ← new-Ix _
  iter₂ ← new-Ix _
  airt ← translate-Arit (arr C) (app (app arit (var (sel-to-str sel name))) (var iter₁))
  let f = λ tmp-name → ((loopnest iter₁ $ (ix-to-str iter₁ tmp-name) <+> "+=" <+> airt) >: (loopnest iter₂ $ assignment (ix-to-str (sel-to-ix sel iter₂) name) (ix-to-str iter₂ tmp-name <+> ";\n")))
  lifetime ← cplx-memory-lifetime (ν u) f
  return (lifetime , loc)


--→(FNum ITy) → (Num OTy) → (Inp ITy OTy) → ?

part-imap-test : String
part-imap-test =
  let fun = part` (bᵣ _⊆_.id (ri _⊆_.id)) (imap` (`λ a ⇒ `λ b ⇒ var b)) in
  proj₁ $ translateInp₂ (num (arr C)) (arr {_} {_} {ι (ν 3) ⊗ (ι (ν 4) ⊗ ι (ν 5))} "mem_loc" idh) fun "fun_name"

pre-ufft-test : String
pre-ufft-test =
  let fun = pre-ufft` dft` in
    proj₁ $ translateInp₂ (num (arr C)) (arr {_} {_} {ι (ν 3) ⊗ (ι (ν 4) ⊗ ι (ν 5))} "mem_loc" idh) fun "fun_name"
-}

{-
fftn-test : String
fftn-test =
  let shp = (ι (ι (ν 2) ⊗ (ι (ν 3)))) ⊗ (ι (ι (ν 4) ⊗ ι (ν 5))) in
  let fun = fftn` shp in
  proj₂ $ translateInp₂ eq (arr "ArName" idh) fun "Fun_Name" --(arr {_} {_} {shp} "mem_loc" idh) fun "fun_name"
  -}

fftn-test′ : String
fftn-test′ =
  let shp = (ι (ι (ν 2) ⊗ (ι (ν 3)))) ⊗ (ι (ι (ν 4) ⊗ ι (ν 5))) in
  let fun = fftn` shp in
  show-inp {_} {_} {_} {eq} fun

entry : String
--entry = proj₁ $ translateInp₂ (num (arr C)) (arr {_} {_} {ι (ν 3)} "mem_loc" idh) dft` "fun_name"
--entry = show-inp {_} {ι (ι (ν 2) ⊗ ι (ν 3))} {_} {up (down transpᵣ)} mini₂ --fftn-test′
--entry = show-inp {_} {ι (ν 2)} {_} {eq} mini₃ 
--entry = show-inp {_} {_} {_} {eq} mini₄
entry = fftn-test′


  --let fun = pre-ufft` {_} {translate-Ty} dft` in

  -- We expect this to partition over 3 and 5, then do the inner most loop over 4


--OLD:
{-
translate-Arit (var x) C = x
translate-Arit (var x) N = x
translate-Arit (var x) (arr nu) = "(WTF 1)"
  --let tm = translate-Arit ? nu
  --"TODO"
translate-Arit (lam x) (arr nu) = "(WTF 2)"
translate-Arit (app (var x) arit₂) nu = "ERROR (Maybe): First class function unhandled" 
translate-Arit (app {τ} (lam {a} {b} x) arit₂) nu = "(TODO: APP LAM)"
 --let r₁ = translate-Arit arit₂ ? in
 --?
translate-Arit (app (app arit₁ arit₃) arit₂) nu = ? --"(TODO: APP APP)"
translate-Arit (sizeN {s = s} arit) N = printf "%u" $ suc $ length s
translate-Arit (posiN arit x) N = "TODO"
translate-Arit (arit₁ *N arit₂) N = 
  let r₁ = translate-Arit arit₁ N in
  let r₂ = translate-Arit arit₁ N in
  parensIfSpace $ r₁ <+> "*" <+> r₂
translate-Arit (arit₁ *C arit₂) C =
  let r₁ = translate-Arit arit₁ C in
  let r₂ = translate-Arit arit₂ C in
  parensIfSpace $ r₁ <+> "*" <+> r₂
translate-Arit (ω` arit₁ arit₂) nu =
  let r₁ = translate-Arit arit₁ N in
  let r₂ = translate-Arit arit₂ N in
  printf "omega(%s, %s)" r₁ r₂
-}

{-
⊂-to-sel : ∀ {l : L} {s : S l} {p : S l} → (s⊂p : s ⊂ p) → State ℕ (Ix (inv-⊂ s⊂p) × Sel s p)
⊂-to-sel (le {l} {s} {.s} {p₂} id) = do
  ix-p₂ ← new-Ix p₂
  return $ ix-p₂ , left ix-p₂ idh
⊂-to-sel (le {l} {s} {p₁} {p₂} (st s⊂p₁)) = do
  ix-inv , sel ← ⊂-to-sel s⊂p₁
  ix-p₂ ← new-Ix p₂
  return $ ix-inv ⊗ ix-p₂ , left ix-p₂ sel
⊂-to-sel (ri {l} {s} {p₁} {.s} id) = do
  ix-p₁ ← new-Ix p₁
  return $ ix-p₁ , right ix-p₁ idh
⊂-to-sel (ri {l} {s} {p₁} {p₂} (st s⊂p₂)) = do
  ix-inv , sel ← ⊂-to-sel s⊂p₂
  ix-p₁ ← new-Ix p₁
  return $ ix-p₁ ⊗ ix-inv , right ix-p₁ sel
⊂-to-sel (bₗ q₁⊂s₁ id) = do
  ix-invₗ , selₗ ← ⊂-to-sel q₁⊂s₁ 
  return $ ix-invₗ , both selₗ idh
⊂-to-sel (bₗ q₁⊂s₁ (st q₂⊂s₂)) = do  
  ix-invₗ , selₗ ← ⊂-to-sel q₁⊂s₁ 
  ix-invᵣ , selᵣ ← ⊂-to-sel q₂⊂s₂ 
  return $ (ix-invₗ ⊗ ix-invᵣ) , both selₗ selᵣ
⊂-to-sel (bᵣ id q₂⊂s₂) = do
  ix-invᵣ , selᵣ ← ⊂-to-sel q₂⊂s₂ 
  return $ ix-invᵣ , both idh selᵣ
⊂-to-sel (bᵣ (st q₁⊂s₁) q₂⊂s₂) = do  
  ix-invₗ , selₗ ← ⊂-to-sel q₁⊂s₁ 
  ix-invᵣ , selᵣ ← ⊂-to-sel q₂⊂s₂ 
  return $ (ix-invₗ ⊗ ix-invᵣ) , both selₗ selᵣ
-}
{-
sel-to-str idh name i = return $ name ++ ix-to-subscripts i
sel-to-str (left x sel) name i = do
  sel-to-str sel (name ++ ix-to-subscripts x) i
sel-to-str (right x sel) name i = do
  str ← sel-to-str sel name i
  return $ str ++ ix-to-subscripts x
sel-to-str (both selₗ selᵣ) name (iₗ ⊗ iᵣ) = do
  a ← sel-to-str selₗ name iₗ
  sel-to-str selᵣ a iᵣ
sel-to-str (chain selₗ selᵣ) name i = do
  a ← sel-to-str selₗ name i
  ?
-}
{-
trans-sel : ∀ {l₁ : L} {s₁ : S l₁} {s₂ : S l₁} {s₃ : S l₁} → Sel s₁ s₂ → Sel s₂ s₃ → Sel s₁ s₃
trans-sel x idh = ?
trans-sel x (left x₁ y) = left x₁ (trans-sel x y)
trans-sel x (right x₁ y) = ?
trans-sel idh (both y y₁) = both y y₁
trans-sel (left x x₁) (both y y₁) = ?
trans-sel (right x x₁) (both y y₁) = both ? (trans-sel x₁ y₁)
trans-sel (both x x₁) (both y y₁) = both (trans-sel x y) ?
-}
{-
trans-sel idh inner-sel = inner-sel
trans-sel (left  ix-p₂ outer-sel) inner-sel = left  ix-p₂ $ trans-sel outer-sel inner-sel
trans-sel (right ix-p₁ outer-sel) inner-sel = right ix-p₁ $ trans-sel outer-sel inner-sel
trans-sel {s₃ = ι s₃} (both {p₂ = p₂} outer-selₗ outer-selᵣ) (left x inner-sel) = left ? $ trans-sel outer-selₗ inner-sel
trans-sel {s₃ = ι s₃} (both outer-selₗ outer-selᵣ) (right x inner-sel) = ?
trans-sel {s₃ = s₃ ⊗ s₄} (both outer-selₗ outer-selᵣ) idh = both ? ?
trans-sel {s₃ = s₃ ⊗ s₄} (both outer-selₗ outer-selᵣ) (left x inner-sel) = both ? ?
trans-sel {s₃ = s₃ ⊗ s₄} (both {s₂ = s₂ ⊗ s₅} outer-selₗ outer-selᵣ) (right x inner-sel) = both (trans-sel outer-selₗ ?) ?
trans-sel {s₃ = s₃ ⊗ s₄} (both outer-selₗ outer-selᵣ) (both inner-selₗ inner-selᵣ) = both (trans-sel outer-selₗ inner-selₗ) (trans-sel outer-selᵣ inner-selᵣ)
-}
--trans-sel (both outer-selₗ outer-selᵣ) idh = both outer-selₗ outer-selᵣ
--trans-sel {s₃ = s₃} (both {p₂ = p₂} outer-selₗ outer-selᵣ) (left ix-s₂ inner-sel) = 
--  let tmp = trans-sel outer-selₗ inner-sel in left ? tmp
--trans-sel (both outer-selₗ outer-selᵣ) (right x inner-sel) = ?
--trans-sel (both outer-selₗ outer-selᵣ) (both inner-sel inner-sel₁) = ?

{-
evaled-to-str (fun num-τ fnum-σ) f = do
  term_name ← fresh-var
  term ← type-var num-τ term_name
  expr ← f term
  final ← evaled-to-str fnum-σ expr
  -- THIS IS WRONG - WE DO NOT HAVE LAMBDA'S IN C
  return $ parens $ "\\" <+> term_name <+> "->" <+> final
-}
```
