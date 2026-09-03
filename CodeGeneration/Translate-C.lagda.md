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
  ix-flat-index : Ix s → String
  ix-flat-index (ν i) = i
  ix-flat-index (ι i) = ix-flat-index i
  ix-flat-index (_⊗_ {s = s} {p} i j) = parensIfSpace 
                                        $   (ix-flat-index i) 
                                        <+> "+" 
                                        <+> parensIfSpace 
                                            ( (showℕ $ clen s) 
                                            <+> "*" 
                                            <+> ix-flat-index j
                                            )
```

```agda
  data InplaceReshape : {s : S ℓ} {s′ : S ℓ′} → Reshape s s′ → Set where
    eq     : ∀ {s  : S ℓ } → InplaceReshape {_} {_} {s} {s} eq
    _∙_    : ∀ {s₁ : S ℓ₁} {s₂ : S ℓ₂} {s₃ : S ℓ₃}     {r₁ : Reshape s₁ s₂} {r₂ : Reshape s₂ s₃} → InplaceReshape r₁ → InplaceReshape r₂ → InplaceReshape (r₂ ∙ r₁)
    _⊕_    : ∀ {s₁ s₂ : S (ss ℓ₁)} {s₃ s₄ : S (ss ℓ₂)} {r₁ : Reshape s₁ s₃} {r₂ : Reshape s₂ s₄} → InplaceReshape r₁ → InplaceReshape r₂ → InplaceReshape (r₁ ⊕ r₂)
    up     : ∀ {r : Reshape s s′} → InplaceReshape r → InplaceReshape (up r)
    down   : ∀ {r : Reshape s s′} → InplaceReshape r → InplaceReshape (down r)
    assoₗ  : ∀ {s₁ s₂ s₃ : S (ss ℓ)} → InplaceReshape (assoₗ {ℓ} {s₁} {s₂} {s₃})
    assoᵣ  : ∀ {s₁ s₂ s₃ : S (ss ℓ)} → InplaceReshape (assoᵣ {ℓ} {s₁} {s₂} {s₃})
    flat   : ∀ {n m : ℕ} → InplaceReshape (flat {n} {m})
    unflat : ∀ {n m : ℕ} → InplaceReshape (unflat {n} {m})

  isInplace : ∀ {s : S ℓ} {s′ : S ℓ′} → (r : Reshape s s′) → Maybe (InplaceReshape r)
  isInplace eq        = just eq
  isInplace (r₁ ∙ r₂) = zipM (isInplace r₂) (isInplace r₁) ⟫= uncurry (just ∘₂′ _∙_) 
  isInplace (r₁ ⊕ r₂) = zipM (isInplace r₁) (isInplace r₂) ⟫= uncurry (just ∘₂′ _⊕_)
  isInplace (up   r)  = isInplace r ⟫= just ∘ up
  isInplace (down r)  = isInplace r ⟫= just ∘ down
  isInplace flat      = just flat
  isInplace unflat    = just unflat
  isInplace swap      = nothing
  isInplace assoₗ     = just assoₗ
  isInplace assoᵣ     = just assoᵣ
  
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

  {-
  a : ∀ {s : S ℓ} (i : P (ι s)) → i ⟨ up eq ∙ down eq ⟩ ≡ i
  a (ι i) = refl
  -}

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

# Translate Ty
We can then start giving Ty it's semantics within C
```
translate-Ty : Ty → Set
translate-Ty C = String
translate-Ty N = String
translate-Ty (ix s) = Ix s
translate-Ty (τ ⇒ σ) = translate-Ty τ → State ℕ (translate-Ty σ)
```

# Arithmetic Evaluator
We can then create an evaluator and translator for our Airthmetic operations.
Our evaluator is going to evaluate all lambda calculus, while the translator 
will stringify this into something which can be used in C. 

```agda
module _ where
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
    return $ ix-flat-index (resh-ix (rev r) i′)
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
    return $ parens $ "minus_omega(" ++ x′ ++ "," <+> y′ ++ ")"
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

  ArCast : Maybe String → S ℓ → String
  ArCast nothing = parens ∘ ArCast (just "")
  ArCast (just memName) = printf "%s (*%s)%s" complex-type memName ∘ ShapeCast

  commentBlock : String → String → String
  commentBlock comment body = printf "//Start: %s\n%s//End: %s\n" comment body comment

  calloc : String → S ℓ → State ℕ (String × String × String)
  calloc type s = do  
    memName ← fresh-var
    let ops = assignment (ArCast (just memName) s) $ (ArCast nothing s) ++ (calloc-op type (clen s))
    let free = printf "free(%s);\n" memName
    return $ memName , ops , free

  -- Placeholder ix
  β : Ix s 
  β {.zz} {ν x} = ν "β"
  β {.(ss _)} {ι s} = ι β
  β {.(ss _)} {s₁ ⊗ s₂} = β ⊗ β


  showIx : Ix s → String 
  showIx {.zz} {ν n} (ν i) = printf "%s < %u, " i (suc n)
  showIx {.(ss _)} {ι s} (ι i) = showIx i
  showIx {.(ss _)} {s ⊗ s₁} (i₁ ⊗ i₂) = showIx i₁ ++ showIx i₂
```

# C Translation

Finally we can move to our C translation

```agda
step₁ : (Ix s → String) → Inp translate-Ty s → (Ix s → String) × (State ℕ String)
step₁ ar (imap` arit) = ar , ops
  where
    ops = do
      i ← new-Ix _
      arit-string ← translate-Arit C (app (app arit (var i)) (var (ar i)))
      return $ commentBlock "imap" $ loopnest i (assignment (ar i) arit-string)
step₁ xs (compose inp₁ inp₂) = op₂ .proj₁ , ops
  where
    op₁ = step₁ xs inp₁
    op₂ = step₁ (op₁ .proj₁) inp₂
    ops = do
      ins₁ ← op₁ .proj₂
      ins₂ ← op₂ .proj₂
      return $ commentBlock "compose" $ ins₁ ++ "//Middle: compose\n" ++ ins₂
step₁ xs (mapSum` {u} arit) = xs , ops
  where
    ops = do
      memName , assign , free ← calloc complex-type (ι (ν u))

      i ← new-Ix (ι (ν u))
      j ← new-Ix (ι (ν u))
      k ← new-Ix (ι (ν u))

      op ← translate-Arit C $ app (app (app arit (`λ l ⇒ (var (xs l)))) (var i)) (var j)
      let body = loopnest j $ loopnest i $ +assignment (ix-to-str i memName) op

      let copyBack = loopnest k $ assignment (xs k) (ix-to-str k memName)
      
      return $ commentBlock "mapSum" $ assign ++ body ++ copyBack ++ free
step₁ xs (copyOut` {_} {s} {p} r₁ r₃ inp) = zs , ops
  where
    zs = xs ∘ resh-ix (up (down (rev (r₃ ∙ r₁))))
    ops = do 
      -- Create the working memory
      workingMem , assign , free ← calloc complex-type p


      i ← new-Ix s
      let copyOutOp = "//" <+> (showResh r₁) ++ "\n" 
                   ++ loopnest i (assignment (ix-to-str (resh-ix r₁ i) workingMem) (xs (ι i)))

      -- Do the inside operations
      let ys , op-f = step₁ (flip ix-to-str workingMem) inp
      op ← op-f

      j ← new-Ix s
      let copyInOp = "//" <+> (showResh r₃) ++ "\n"
                  ++ loopnest j (assignment (xs (ι j)) (ix-to-str (resh-ix (rev r₃) j) workingMem))

      let ops = assign ++ copyOutOp ++ op ++ copyInOp ++ free
      return $ commentBlock "copyOut" $ ops

      {-
      -- Create the working memory we copy in to and out of 
      workingMem , assign , free ← calloc complex-type p

      -- Copy out into the working memory, applying r₁ as we do so
      i ← new-Ix p
      let out-op = "//" <+> (showResh r₁) ++ "\n"
                  ++ assignment (ix-to-str i workingMem) (xs (resh-ix (up (rev r₁)) i))
      let out = (loopnest i out-op) ++ "\n"

      -- Do the inside operations
      let ys , op-f = step₁ r₂ (flip ix-to-str workingMem) inp
      op ← op-f
      
      --let maybeIsinplace = isInplace (r₃ ∙ r₂ ∙ r₁) -- this should never be not just, unless the outer most or inner most shape is just ι

      ------------- BELOW THIS LINE IS WHERE WE CURRENTLY GO WRONG ------------
      ---------------------------- I Think ------------------------------------
      ------------------- Or in a function called below ofc -------------------
      -- Re cast --
      memName₂ ← fresh-var
      let re-cast = "// SOMETHING GOES WRONG HERE:\n" 
                    ++ "//" <+> (showResh r₃) ++ "\n"
                    ++ assignment (ArCast (just memName₂) s′) (ArCast nothing s′ <+> workingMem)

      j ← new-Ix s′
      let inn-op = assignment (zs (resh-ix (up eq) j)) (ix-to-str j memName₂)
      let inn = (loopnest j inn-op)

      return $ commentBlock "copyOut" $ assign ++ out ++ op ++ re-cast ++ inn ++ free
      -}
step₁ xs (part` {_} {s} {p} s⊂p inp) = xs , ops
  where
    ops = do
      i ← new-Ix s
      let ys = λ j → xs (resh-ix (rev (to-resh s⊂p)) (i ⊗ j))

      let _ , op-f = step₁ ys inp
      op ← op-f

      return $ commentBlock "part" $ loopnest i op

inp→f : Inp translate-Ty s → String → String
inp→f {_} {s} inp function-name = runState inp→f′ 0 .proj₂
  where
    inp→f′ : State ℕ String
    inp→f′ = do
      var-name ← fresh-var
      let _ , f = step₁ (flip ix-to-str var-name) inp
      body ← f
      return $ printf "void %s(%s) {\n%s}\n" function-name (ArCast (just var-name) s) body 

inp-signature : Inp translate-Ty s → String → String
inp-signature {_} {s} inp function-name = printf "void %s%s;\n" function-name (ArCast nothing s)

sizeDef : S ℓ → String → String
sizeDef s name =     (printf "#ifndef %s_SIZE\n" name)
                  ++ (printf "#define %s_SIZE %u\n" name (clen s))
                  ++ (printf "typedef complex real (*%s_TYPE)%s;\n" name (ShapeCast s))
                  ++ "#endif\n"
```

# Testing

```agda
module _ where
  -- Name inspired by hit song uptown funk, which sounds similar to up-down-funk
  funk : ∀ {s p : S ℓ} → Reshape s p → Reshape (ι s) (ι p)
  funk r = up (down r)

  mini₃ : ∀ {s : S zz} → Inp translate-Ty (ι s) 
  mini₃ {ν u} = mapSum` (`λ x ⇒ `λ i ⇒ var x)

  mini₄ : Inp translate-Ty (ι (ν 3) ⊗ ι (ν 5)) 
  mini₄ = part` (ri _⊆_.id) (imap` (`λ i ⇒ `λ x ⇒ var x *C (ω` (sizeN (var i)) (posiN (var i) eq))))

  open import Matrix.Leveled.NatMon-Change-Major
  open Change-Major ℕ-CM

  id` : Inp translate-Ty s 
  id` = imap` (`λ i ⇒ `λ x ⇒ var x)

  -- Working
  test₃ : String
  test₃ = inp→f (test₃′ (ι (ι (ν 1)) ⊗ ι (ι (ν 2)))) "CMtTest3" 
    where
      test₃′ : ∀ (s : S (ss (ss zz))) → Inp translate-Ty (ι s) 
      test₃′ s = copyOut` (rev CMᵗ) CMᵗ id`

  -- Working
  test₄ : String
  test₄ = inp→f (test₄′ (ι (ι (ν 1)) ⊗ ι (ι (ν 2)))) "CMtTest4" 
    where
      test₄′ : ∀ (s : S (ss (ss zz))) → Inp translate-Ty (ι s) 
      test₄′ s = copyOut` (rev transpᵣ) CMᵗ id`

  test₅ : String
  test₅ = inp→f (test₅′ (ι ((ι (ν 1)) ⊗ (ι (ν 2))))) "CMtTest5" 
    where
      test₅′ : ∀ (s : S (ss (ss zz))) → Inp translate-Ty (ι s) 
      test₅′ s = copyOut` eq eq id`

  fftn-test-sig′ : S (ss (ss zz)) → String
  fftn-test-sig′ s = inp-signature (fftn` s) "fftn"

  fftn-test′ : S (ss (ss zz)) → String
  fftn-test′ s =
    --let shp = 
    let fun = fftn` s in
    inp→f fun "fftn"

entry : String
--entry = proj₁ $ translateInp₂ (num (arr C)) (arr {_} {_} {ι (ν 3)} "mem_loc" idh) dft` "fun_name"
--entry = show-inp {_} {ι (ι (ν 2) ⊗ ι (ν 3))} {_} {up (down transpᵣ)} mini₂ --fftn-test′
--entry = show-inp {_} {ι (ν 2)} {_} {eq} mini₃ 
--entry = show-inp {_} {_} {_} {eq} mini₄
entry = fftn-test′ ((ι (ι (ν 2) ⊗ (ι (ν 3)))) ⊗ (ι (ι (ν 4) ⊗ ι (ν 5))))
```
