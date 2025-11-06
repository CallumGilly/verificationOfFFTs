--{-# OPTIONS --backtracking-instance-search #-}
{-# OPTIONS --guardedness #-}
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin using (Fin; zero; suc; cast; toℕ)
open import Data.Fin.Properties
open import Function

open import Real using (Real)
open import Complex using (Cplx)

open import Matrix renaming (length to size)
open import Matrix.Reshape
open import Matrix.NonZero 

-- FIXME: these have to be actual definitions!
_ᵗ : Shape → Shape
_ᵗ = recursive-transpose

nzᵗ : NonZeroₛ s → NonZeroₛ (s ᵗ)
nzᵗ = nonZeroₛ-s⇒nonZeroₛ-sᵗ

nz-# : NonZeroₛ s → NonZero (size s)
nz-# = nonZeroₛ-s⇒nonZero-s


infixr 5 _⇒_
data Ty : Set where
  C   : Ty
  ix  : Shape → Ty
  _⇒_ : Ty → Ty → Ty

ar : Shape → Ty → Ty
ar s X = ix s ⇒ X

variable
  τ σ δ : Ty

data Num : Ty → Set where
  C   : Num C
  arr : Num τ → Num (ix s ⇒ τ)

data Fut : Ty → Set where
  num : Num τ → Fut τ
  fun : Num τ → Fut σ → Fut (τ ⇒ σ)

infixl 3 _`$_
data E (V : Ty → Set) : Ty → Set where
  `     : V τ → E V τ
  `lam  : (V τ → E V σ) → E V (τ ⇒ σ)
  _`$_  : E V (τ ⇒ σ) →  E V τ → E V σ
  _`⊗_  : E V (ix s) → E V (ix p) → E V (ix (s ⊗ p))
  `fst  : E V (ix (s ⊗ p)) → E V (ix s)
  `snd  : E V (ix (s ⊗ p)) → E V (ix p)
  `swap : E V (ar (s ⊗ p) τ) → E V (ar (p ⊗ s) τ)
  `sum  : E V (ar (ι n) C) → E V C
  -- Too specialised?
  `ω    : (n : ℕ) → .⦃ NonZero n ⦄ → E V (ix (s ⊗ p)) → E V C
  _`*_  : (a b : E V C) → E V C

infix 1 `lam
syntax `lam (λ x → e) = `λ x ⇒ e

variable
  V : Ty → Set

--data First-Order (e : E V τ) : Set where
  

{-
instance
  out : ⦃ NonZeroₛ (ι n) ⦄ → NonZero n
  out ⦃ ι x ⦄ = x

  ι-ins : ⦃ NonZero n ⦄ → NonZeroₛ (ι n)
  ι-ins ⦃ p ⦄ = ι p

  ⊗-ins : ⦃ NonZeroₛ s ⦄ → ⦃ NonZeroₛ p ⦄ → NonZeroₛ (s ⊗ p)
  ⊗-ins ⦃ p ⦄ ⦃ q ⦄ = p ⊗ q

  ᵗ-ins : ⦃ NonZeroₛ s ⦄ → NonZeroₛ (s ᵗ)
  ᵗ-ins ⦃ p ⦄ = nonZeroₛ-s⇒nonZeroₛ-sᵗ p

  --{-# INCOHERENT ι-ins ᵗ-ins out ⊗-ins #-} 
-}

`mapₐ : E V ((τ ⇒ σ) ⇒ ar s τ ⇒ ar s σ)
`mapₐ = `λ f ⇒ `λ a ⇒ `λ i ⇒ ` f `$ (` a `$ ` i)

`map : E V ((τ ⇒ σ) ⇒ τ ⇒ σ)
`map = `λ f ⇒ `λ a ⇒ ` f `$ ` a

`nest : E V (ar (s ⊗ p) τ ⇒ (ar s (ar p τ)))
`nest = `λ a ⇒ `λ i ⇒ `λ j ⇒ ` a `$ (` i `⊗ ` j)

`unnest : E V (ar s (ar p τ) ⇒ ar (s ⊗ p) τ)
`unnest = `λ a ⇒ `λ i ⇒ ` a `$ `fst (` i) `$ `snd (` i)

`dft : ⦃ NonZero n ⦄ → E V (ar (ι n) C ⇒ ar (ι n) C)
`dft {n = n} = `λ a ⇒ `λ j ⇒ `sum (`λ k ⇒ (` a `$ ` k) `* `ω n (` k `⊗ ` j))


`twid : ⦃ NonZeroₛ (s ⊗ p) ⦄ → E V (ar (s ⊗ p) C)
`twid {s = s}{p} ⦃ nz ⦄ = `λ i ⇒ `ω (size (s ⊗ p)) ⦃ nz-# nz ⦄ (` i)

`fft : ⦃ NonZeroₛ s ⦄ → E V (ar s C ⇒ ar (s ᵗ) C)
`fft ⦃ ι nz    ⦄ = `dft ⦃ nz ⦄
`fft ⦃ ns ⊗ np ⦄ = `λ a ⇒ let 
                            a'  = `swap (` a)
                            r1  = `unnest `$ (`mapₐ `$ `fft ⦃ ns ⦄ `$ (`nest `$ a'))
                            rt  = `λ i ⇒ (r1 `$ ` i) `* (`twid ⦃ np ⊗ nzᵗ ns ⦄ `$ ` i)
                            rt' = `swap rt
                            r2  = `mapₐ `$ `fft ⦃ np ⦄ `$ (`nest `$ rt')
                            r2' = `swap (`unnest `$ r2)
                          in r2'
                          
module Interp (real : Real) (cplx : Cplx) where
  open Cplx cplx renaming (_+_ to _+𝕔_; _*_ to _*𝕔_)
  open Real.Real real using (_ᵣ)
  
  open import Matrix.Equality
  open import FFT cplx
  open import Proof cplx

  Sem : Ty → Set
  Sem C = ℂ
  Sem (ix x) = Position x
  Sem (τ ⇒ σ) = Sem τ → Sem σ

  fst : Position (s ⊗ p) → Position s
  fst (i ⊗ j) = i

  snd : Position (s ⊗ p) → Position p
  snd (i ⊗ j) = j

  interp : E Sem τ → Sem τ
  interp (` x) = x
  interp (`lam f) x = interp (f x)
  interp (e `$ e₁) = interp e (interp e₁)
  interp (e `⊗ e₁) = interp e ⊗ interp e₁
  interp (`fst e) = fst (interp e)
  interp (`snd e) = snd (interp e)
  interp (`swap e) (i ⊗ j) = interp e (j ⊗ i)
  interp (`sum e) = sum (interp e)
  interp (`ω n e) = -ω n (offset-prod (interp e))
  interp (e `* e₁) = interp e *𝕔 interp e₁

  -- I hate stupid instances!
  efft-ok :  ⦃ _ : NonZeroₛ s ⦄ → ∀ a → FFT′ {s} a ≅ interp `fft a
  efft-ok ⦃ ι nz    ⦄ a i       = refl
  efft-ok ⦃ ns ⊗ np ⦄ a (i ⊗ j) =
    begin
      _ ≡⟨ FFT′-cong ⦃ np ⦄ (λ k → cong₂ _*𝕔_ (efft-ok ⦃ ns ⦄ _ j) refl) i ⟩
      _ ≡⟨ efft-ok ⦃ np ⦄ _ i ⟩
      _
    ∎ where open ≡-Reasoning


module ShowC where
  open import Data.Nat
  open import Data.Bool
  open import Data.String hiding (show)
  open import Data.Product
  open import Data.Maybe hiding (_>>=_)
  open import Text.Printf
  open import Relation.Nullary
  open import Effect.Monad 
  open import Effect.Monad.State
  open RawMonadState {{...}}
  open RawMonad {{...}} hiding (_⊗_)
  instance
    _ = monad
    _ = monadState 

  data Ix : Shape → Set where 
    ι   : String → Ix (ι n)
    _⊗_ : Ix s → Ix p → Ix (s ⊗ p)

  Val : Ty → Set
  Val C = String
  Val (ix s) = Ix s
  Val (τ ⇒ σ) = Val τ → State ℕ (String × Val σ) -- ADDED 

  data Op : Set where
    += : Op
    ≔  : Op

  op-str : Op → String
  op-str += = "+="
  op-str ≔  = "="

  fresh : ℕ → String
  fresh = printf "x_%u"

  fresh-var : State ℕ String
  fresh-var = do
    n ← get
    modify suc
    return (fresh n)

  offset : Ix s → String
  offset (ι x) = x
  offset {s ⊗ p} (i ⊗ j) = printf "((%u * %s) + %s)" (size p) (offset i) (offset j)

  to-sel : Ix s → String → String
  to-sel i a = a ++ ix-join (ix-map (printf "[%s]") i) ""
    where
      ix-join : Ix s → (d : String) → String
      ix-join (ι x) d = x
      ix-join (i ⊗ j) d = ix-join i d ++ d ++ ix-join j d
      
      ix-map : (String → String) → Ix s → Ix s
      ix-map f (ι x) = ι (f x)
      ix-map f (i ⊗ j) = ix-map f i ⊗ ix-map f j


  omega : ℕ → Ix (s Shape.⊗ p) → Val C
  omega sz (i ⊗ j) = printf "minus_omega(%u,(%s * %s))" 
                             sz (offset i) (offset j)

  -- We don't need to return stateful result right now,
  -- but conceptually, we might need free variables fro higher-oreder
  -- cases if we ever want to support them.
  num-var : Num τ → (n : String) → State ℕ (Val τ)
  num-var C n = return n
  num-var (arr p) n = return λ i → do
    nvp ← num-var p (to-sel i n)
    return ("" , nvp)

  to-str : Fut τ → Val τ → (res : String) → Op → State ℕ String

  to-val : E Val τ → {- (res op : String)  → -} State ℕ (String × Val τ)
  to-val (` x)     = return ( "" , x)
  to-val (`lam x) = do
    let f t = to-val (x t)
    return ("" , f )
  to-val (e `$ e₁) = do
    (d , f) ← to-val e
    (p , x) ← to-val e₁
    pre , q ← f x
    return ( d ++ p ++ pre , q ) -- Consider order here
  to-val (l `⊗ r) = do
    (ld , lx) ← to-val l
    (rd , rx) ← to-val r
    return (ld ++ rd , lx ⊗ rx)
  to-val (`fst e)  = do
    d , (i ⊗ _) ← to-val e
    return ( d , i )
  to-val (`snd e)  = do
    d , (_ ⊗ j) ← to-val e
    return ( d , j )
  to-val (`swap e) = do
    d , a ← to-val e
    return ( d , λ{(j ⊗ i) → a (i ⊗ j)})
  to-val (`sum e) = do
    fresh-res ← fresh-var 
    def , array-summed ← to-val e
    s ← to-str (num (arr C)) array-summed fresh-res +=
    return (def ++ (printf "complex float %s = 0;\n" fresh-res) ++ s , fresh-res)
  to-val (`ω n e)  = do
    (d , k) ← to-val e
    return ( d , omega n k )
  to-val (l `* r) = do
    ld , lx ← to-val l
    rd , rx ← to-val r
    return (ld ++ rd , printf "(%s * %s)" lx rx)

  {- This doesn't currently work
  ty-to-cType : Ty → (String → String)
  ty-to-cType C = printf "float complex %s"
  ty-to-cType (ix x) = printf "float complex *%s"
  ty-to-cType (x ⇒ x₁) = printf "(%s to %s) %s" (ty-to-cType x "a") (ty-to-cType x₁ "b")

  --printf "float complex %s" -- TODO: Make this not this because this is wrong but is quick, dirty and passes a LGTM
  -}

  for-template : String → ℕ → String → String
  for-template i n expr = printf "for (int %s = 0; %s < %u; %s++) {\n%s\n}" i i n i expr

  generateIx : (s : Shape) → State ℕ (Ix s)
  generateIx (ι n)   =
    do
      m ← get 
      modify suc
      let ix = fresh m
      return (ι ix)
  generateIx (s ⊗ p) =
    do
      iₗ ← generateIx s
      iᵣ ← generateIx p
      return (iₗ ⊗ iᵣ)

  loop-nest-helper : (s : Shape) → Ix s → (String → String)
  loop-nest-helper (ι n    ) (ι i    ) = for-template i n
  loop-nest-helper (sₗ ⊗ sᵣ) (iₗ ⊗ iᵣ) = loop-nest-helper sₗ iₗ ∘ loop-nest-helper sᵣ iᵣ

  loop-nest : Fut τ → (res : String) → Op → (Ix s → State ℕ (String × Val τ)) → State ℕ String
  loop-nest {s = s} fut res += body =
    do 
      i ← generateIx s
      body-pre , body-val ← body i
      body-ass ← to-str fut body-val (res) +=
      return $ loop-nest-helper s i (body-pre ++ body-ass)
  loop-nest {s = s} fut res ≔  body =
    do 
      i ← generateIx s
      body-pre , body-val ← body i
      body-ass ← to-str fut body-val (to-sel i res) ≔
      return $ loop-nest-helper s i (body-pre ++ body-ass)

  shape-to-arg : String → Shape → String
  shape-to-arg res (ι _)   = printf "(*%s)" res
  shape-to-arg res (s ⊗ p) = shape-to-arg res s ++ helper p
    where
      helper : Shape → String
      helper (ι n)   = printf "[%u]" n
      helper (s ⊗ p) = helper s ++ helper p

  to-str (num C) v res op = return $ printf "%s %s %s;" res (op-str op) v
  to-str (num (arr x)) v res op = loop-nest (num x) res op v
  -- We currently only want to deal with functions which accept and array, and 
  -- return an array, for now therefore we can throw an error instead of producing
  -- code for all other inputs
  to-str (fun {C           }   {σ           } _ _) _ _ _ = return $ printf "ERROR - Unhandled Function type 1"
  to-str (fun {ix _ ⇒ ix _ }   {σ           } _ _) _ _ _ = return $ printf "ERROR - Unhandled Function type 2"
  to-str (fun {ix _ ⇒ _ ⇒ _}   {σ           } _ _) _ _ _ = return $ printf "ERROR - Unhandled Function type 3"
  to-str (fun {ix _ ⇒ C    }   {C           } _ _) _ _ _ = return $ printf "ERROR - Unhandled Function type 4"
  to-str (fun {ix _ ⇒ C    }   {ix _        } _ _) _ _ _ = return $ printf "ERROR - Unhandled Function type 5"
  to-str (fun {ix _ ⇒ C    }   {C ⇒ _       } _ _) _ _ _ = return $ printf "ERROR - Unhandled Function type 6"
  to-str (fun {ix _ ⇒ C    }   {(_ ⇒ _) ⇒ _ } _ _) _ _ _ = return $ printf "ERROR - Unhandled Function type 7"
  to-str (fun {ix _ ⇒ C    }   {ix _ ⇒ ix _ } _ _) _ _ _ = return $ printf "ERROR - Unhandled Function type 8"
  to-str (fun {ix _ ⇒ C    }   {ix _ ⇒ _ ⇒ _} _ _) _ _ _ = return $ printf "ERROR - Unhandled Function type 9"
  to-str (fun {ix s ⇒ C    } σ@{ix s₁ ⇒ C} inp out) val res op =
    do
      n ← get
      modify suc
      let arg-name = (fresh n)
      arg ← num-var inp arg-name
      str-pre , β-val ← val arg
      str-val ← to-str {σ} out β-val res op
      return $ printf "void %s(complex float %s, complex float %s) {\n%s\n}" 
        res 
        (shape-to-arg arg-name s) 
        (shape-to-arg res s₁) 
        (str-pre ++ str-val)

  show : Fut τ → (∀ {V} → E V τ) → String → String
  show p e res = runState ( 
      do 
          (deps , val) ← to-val e
          result ← to-str p val res ≔
          return $ deps ++ result
    ) 0 .proj₂

module Tests where
  open import Data.Empty
  open import Relation.Nullary
  open import Data.String hiding (show)

  open ShowC

  sh : Shape
  sh = (ι 5 ⊗ ι 6) ⊗ ι 7

  sh-big : Shape
  sh-big = ((ι 5 ⊗ ι 7) ⊗ ι 8) ⊗ (ι 9 ⊗ ι 10)

  sh-mini : Shape
  sh-mini = ι 2 ⊗ (ι 3 ⊗ ι 3)

  fft : E V _
  fft = `fft {s = sh} ⦃ (ι _ ⊗ ι _) ⊗ ι _ ⦄

  fft-big : E V _
  fft-big = `fft {s = sh-big} ⦃ ((ι _ ⊗ ι _) ⊗ ι _) ⊗ (ι _ ⊗ ι _) ⦄
  
  fft-mini : E V _
  fft-mini = `fft {s = sh-mini} ⦃ ι _ ⊗ (ι _ ⊗ ι _) ⦄

  -- The inner map should normalise away
  test : E V (ar sh C ⇒ ar sh C) 
  test = `λ a ⇒ `mapₐ `$ (`λ z ⇒ ` z) `$ ` a

  -- We can define this expression, but we can't show that
  -- its type is Fut
  scary : E V (ix sh ⇒ ix sh)
  scary = `λ i ⇒ ` i

  _ : Fut (ix s ⇒ ix s) → ⊥
  _ = λ { (num (arr ())) }

  -- This one is ok, because scary will be inlined
  test₁ : E V (ar sh C ⇒ ar sh C) 
  test₁ = `λ a ⇒ `λ i ⇒ ` a `$ (scary `$ ` i) 

  -- Can't have Fut of that type
  test₂ : E V ((C ⇒ C) ⇒ _) 
  test₂ = `λ f ⇒ ` f

  _ : Fut ((C ⇒ C) ⇒ C) → ⊥
  _ = foo where
      foo : _
      foo (num ())
      foo (fun () _)

  -- This is fine
  test₃ :  E V (ar sh C ⇒ ar _ C) 
  test₃ = `λ a ⇒ `swap (` a)

  test₄ : E V (ar (ι 10 ⊗ ι 10) C ⇒ C) 
  test₄ = `λ a ⇒ `sum (`λ i ⇒ `sum (`λ j ⇒ ` a `$ (` j `⊗ ` i)))

  getType : E V τ → Ty
  getType {τ = τ} _ = τ 

  isNum : (τ : Ty) → Dec (Num τ)
  isNum C = yes C
  isNum (ix x) = no λ ()
  isNum (C ⇒ σ) = no λ ()
  isNum ((_ ⇒ _) ⇒ σ) = no λ ()
  isNum (ix x ⇒ σ) with isNum σ
  ... | yes p = yes (arr p)
  ... | no ¬p = no λ { (arr p) → ¬p p }

  isFut : (τ : Ty) → Dec (Fut τ)
  isFut C = yes (num C)
  isFut (ix x) = no λ { (num ()) }
  isFut (C ⇒ σ) with isFut σ
  ... | no ¬p = no λ { (fun _ p) → ¬p p }
  ... | yes p = yes (fun C p) 
  isFut (ix x ⇒ σ) with isNum σ
  ... | no ¬p = no λ { (num (arr p)) → ¬p p }
  ... | yes p = yes (num (arr p))
  isFut (τ@(_ ⇒ _) ⇒ σ) with isNum τ
  ... | no ¬p = no λ { (fun p _) → ¬p p }
  ... | yes p with isFut σ
  ... | no ¬q = no λ { (fun _ q) → ¬q q }
  ... | yes q = yes (fun p q)

  show-test : (∀ {V} → E V τ) → True (isFut τ) → String
  show-test {τ = τ} e t with isFut τ
  ... | yes p = show p e "fft"

  res = show-test fft-mini _

module Print where
  open ShowC
  open Tests

  open import IO using (IO; run; Main; _>>_; _>>=_)
  open import IO.Finite using (putStrLn)
  open import Data.Unit.Polymorphic.Base using (⊤)
  open import Data.String hiding (show)

  main : Main
  main = run $ putStrLn $  "#include <complex.h>\n" 
                        ++ "#include \"../src/minus-omega.h\"\n"
                        ++ res

