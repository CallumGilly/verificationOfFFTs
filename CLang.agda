--{-# OPTIONS --backtracking-instance-search #-}
{-# OPTIONS --guardedness #-}

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties using (*-comm)
open import Data.Fin using (Fin; zero; suc; cast; toℕ)
open import Function

open import Real using (Real)
open import Complex using (Cplx)

open import Matrix renaming (length to size; nest to nestₛ; unnest to unnestₛ)
open import Matrix.Reshape
open import Matrix.NonZero 
open import Matrix.SubShape


-- FIXME: these have to be actual definitions!
_ᵗ : Shape → Shape
_ᵗ = recursive-transpose

nzᵗ : {s : Shape} → NonZeroₛ s → NonZeroₛ (s ᵗ)
nzᵗ = nonZeroₛ-s⇒nonZeroₛ-sᵗ

nz-# : {s : Shape} → NonZeroₛ s → NonZero (size s)
nz-# = nonZeroₛ-s⇒nonZero-s

private variable
  s s₁ s₂ q p q₁ q₂ : Shape
  n : ℕ

infixr 5 _⇒_
data Ty : Set where
  C   : Ty
  R   : Ty
  ix  : Shape → Ty
  _⇒_ : Ty → Ty → Ty

ar : Shape → Ty → Ty
ar s X = ix s ⇒ X

data Component : Set where
  REAL : Component
  IMAG : Component

variable
  τ σ δ ψ : Ty

data Num : Ty → Set where
  C   : Num C
  R   : Num R
  arr : Num τ → Num (ix s ⇒ τ)

data Fut : Ty → Set where
  num : Num τ → Fut τ
  fun : Num τ → Fut σ → Fut (τ ⇒ σ)

LANES : ℕ
LANES = 4

BLOCKS : ℕ
BLOCKS = 8

_ : BLOCKS % LANES ≡ 0
_ = refl

data ?SIMD : Shape → Set where
  ι : (m : ℕ) → ?SIMD (ι (m * LANES))
  _⊗_ : ?SIMD s → ?SIMD p → ?SIMD (s ⊗ p)

--data Vec-AR : Shape → Set where
--  vid : Vec-AR (ι LANES)
--  mul : (n : ℕ) → Vec-AR (ι (n * LANES))
--  mul′ : (n : ℕ) → Vec-AR (ι n ⊗ ι LANES)
--  --left  : Vec-AR s₁ → Vec-AR (s₁ ⊗ s₂)
--  right : Vec-AR s₂ → Vec-AR (s₁ ⊗ s₂)

--is-Vec-AR : (s : Shape) → Dec (Vec-AR s)
--is-Vec-AR (ι x) with x ≟ LANES | ?
--... | yes refl | _ = yes vid
--... | no ¬a    | tmp = ?
--is-Vec-AR (s ⊗ s₁) = ?

--NonZeroₛₛ : ( s : SIMD-Shape ) → Set
--NonZeroₛₛ = ?

--assoᵣ : Reshape (s ⊗ (p ⊗ q)) ((s ⊗ p) ⊗ q)
--assoᵣ {s} {p} {q} = ?

infixl 2 _>>>_
data Inp : Ty → Ty → Set where
  dft  : NonZero n → Inp (ar (ι 2 ⊗ ι n) R) (ar (ι 2 ⊗ ι n) R)
  --dft′  : NonZero n → Inp (ar (ι 2 ⊗ (ι n ⊗ ι LANES)) R) (ar (ι 2 ⊗ (ι n ⊗ ι LANES)) R)
  --dft′′  : NonZero n → Inp (ar (ι 2 ⊗ ι (n * LANES)) R) (ar (ι 2 ⊗ ι (n * LANES)) R)
  --dft′′  : NonZero n → Inp (ar (ι 2 ⊗ (ι n ⊗ μ)) R) (ar (ι 2 ⊗ (ι n ⊗ μ)) R)
  pretwid : ⦃ NonZeroₛ (s ⊗ p) ⦄ → ?SIMD (s ⊗ p) → Inp (ar (ι 2 ⊗ (s ⊗ p)) R) (ar (ι 2 ⊗ (s ⊗ p)) R) 
  twid : ⦃ NonZeroₛ (s ⊗ p) ⦄ → Inp (ar (ι 2 ⊗ (s ⊗ p)) R) (ar (ι 2 ⊗ (s ⊗ p)) R) 
  --izip : Neex Expr → Inp (ar s τ) (ar s σ)
  
  part : Inp (ar s τ) (ar q τ) → s ⊂ p → Inp (ar p τ) (ar p τ)  
  --part : Inp (ar q₁ τ) (ar q₂ τ) → (q₁⊂s₁ : q₁ ⊂ s₁) → (q₂⊂s₂ : q₂ ⊂ s₂) → (inv-⊂ q₁⊂s₁ ≡ inv-⊂ q₂⊂s₂) → Inp (ar s₁ τ) (ar s₂ τ)  

  _>>>_ : Inp τ δ → Inp δ σ → Inp τ σ

  copy : Reshape s p → Inp (ar s τ) (ar p τ)

data Stmt (V : Ty → Set) : Ty → Set

data Exp (V : Ty → Set) : Ty → Set where
  var : V τ → Exp V τ
  ixr : Exp V (ix s) → Reshape p s → Exp V (ix p)
  sel : Exp V (ar s τ) → Exp V (ix s) → Exp V τ

data View (V : Ty → Set) : Ty → Ty → Set where
  nest   : View V (ar (s ⊗ p) τ)  (ar s (ar p τ))
  unnest : View V (ar s (ar p τ)) (ar (s ⊗ p) τ)
  vmap   : View V τ σ  → View V (ar s τ) (ar s σ)
  _∙_    : View V σ δ  → View V τ σ → View V τ δ
  resh   : Reshape s p → View V (ar s τ) (ar p τ)

data Stmt V where
  dft : Stmt V (ar (ι 2 ⊗ ι n) R)
  twid : Stmt V (ar (ι 2 ⊗ (s ⊗ p)) R)

  write : Exp V τ → Stmt V τ

  view : View V τ σ → Stmt V σ → Stmt V τ

  pfor : (V (ix s) → Stmt V τ) → Stmt V (ar s τ)
  
  _>>>_ : Stmt V τ → Stmt V τ → Stmt V τ

  copy : (V (ar s R) → Stmt V (ar s R)) → Stmt V (ar s R)
 

--``ffti : NonZeroₛ s → Inp (ar ((ι 2 ⊗ s) ⊗ (ι BLOCKS ⊗ ι LANES)) R) (ar ((ι 2 ⊗ s) ⊗ (ι BLOCKS ⊗ ι LANES)) R)
{-
From FFTN:
    #define BLOCK 8
    #define LANES 4
    assert BLOCK % LANES ≡ 0

Assuming an input (ι 2 ⊗ s), the value of each leaf in s must be ≥ BLOCK
  n ≥ BLOCK ∀ ι n ∈ s 

Following FFTN (fftn.c:157)
- Setup, splitting the input into s ≡ (n₁ ⊗ n₂ ⊗ n₃) 
  - Chunk = (n₂ * n₃ / BLOCK) ⌈/⌉ processCount*10 
  for j ∈ n₂ * n₃ step BLOCK

     <- n₂ ->

    /------/|     ^
   /      / |     |
  /------/ /|     |
  | | | | / |     |
  -------/ /|     n₁
  | | | | / |     |
  -------/ /|     |
  | | | | / |     |
  -------/ /|     |
  | | | | / |     ⌄
  -------/ /   
  | | | | /   n₃
  -------/ 



-}

--`uffti : NonZeroₛ s → Inp (ar (ι 2 ⊗ (s ᵗ)) R) (ar (ι 2 ⊗ s) R)
--`uffti (ι nz)      = dft nz
--`uffti (_⊗_ {s} {p} nz-s nz-p) =
--  part (`uffti nz-s) (bothᵣ idh (right idh)) ? ?
--  >>> twid
--  >>> part (`uffti nz-p) (bothᵣ idh (left idh)) ? ?
--  >>> ? --copy (recursive-transpose-invᵣ ∙ eq ⊕ recursive-transposeᵣ)
--  where instance
--    _ : NonZeroₛ (recursive-transpose p ⊗ recursive-transpose s)
--    _ = (nonZeroₛ-s⇒nonZeroₛ-sᵗ (nz-s ⊗ nz-p))

--TODO : ?
-- Why does this not give the correct results...

`uffti′ : NonZeroₛ s → ?SIMD s → Inp (ar (ι 2 ⊗ s) R) (ar (ι 2 ⊗ s) R)
`uffti′ (ι nz) _ = dft nz
`uffti′ {s ⊗ p} (_⊗_ {p = p} nzs nzp) (pred₁ ⊗ pred₂) = 
      part (`uffti′ {s} nzs pred₁) (bothᵣ idh (left  idh))
  >>> pretwid ⦃ nzs ⊗ nzp ⦄ (pred₁ ⊗ pred₂)
  >>> part (`uffti′ {p} nzp pred₂) (bothᵣ idh (right idh))

fft′ : ∀ {s : Shape} → Inp (ar s ℝ) (ar s ℝ)
fft′ {ι _}   = dft 
fft′ {s ⊗ p} = 
      part fft′ (bothᵣ idh (left  idh))
  >>> pretwid
  >>> part fft′ (bothᵣ idh (right idh))
  >>> copy swap

`uffti : NonZeroₛ s → ?SIMD s → Inp (ar (ι 2 ⊗ s) R) (ar (ι 2 ⊗ (s ᵗ)) R)
`uffti {s} nz-s pred = `uffti′ nz-s pred
                  >>> copy (eq ⊕  recursive-transposeᵣ)
                

--`uffti {s} nz-s = copy (eq ⊕ recursive-transposeᵣ) 
--                >>> `uffti′ (nonZeroₛ-s⇒nonZeroₛ-sᵗ nz-s) 
--                >>> copy (eq ⊕ (♯ ∙ (reindex (sym $ |s|≡|sᵗ| {s})) ∙ ♭))

`ffti : NonZeroₛ s → ?SIMD s → Inp (ar (ι 2 ⊗ s) R) (ar (ι 2 ⊗ (s ᵗ)) R)
`ffti  = `uffti
--TODO = ?

private variable
  n₁ n₂ n₃ : ℕ

`fftCube : NonZero n₁ → NonZero n₂ → NonZero n₃ → Inp (ar (ι 2 ⊗ (ι n₁ ⊗ (ι n₂ ⊗ ι n₃))) R) (ar (ι 2 ⊗ (ι n₁ ⊗ (ι n₂ ⊗ ι n₃))) R)
`fftCube {n₁} {n₂} {n₃} nz-n₁ nz-n₂ nz-n₃ = 
      part (dft nz-n₁)                  (bothᵣ idh (left idh))
  >>> twid ⦃ ι nz-n₁ ⊗ (ι nz-n₂ ⊗ ι nz-n₃) ⦄
  >>> part (dft nz-n₂)                  (bothᵣ idh (right (srt (left idh))))
  >>> part (twid ⦃ ι nz-n₂ ⊗ ι nz-n₃ ⦄) (bothᵣ idh (right idh))
  >>> part (dft nz-n₃)                  (bothᵣ idh (right (srt (right idh))))
  >>> copy (eq ⊕ (♯ ∙ reindex (sym $ |s|≡|sᵗ| {ι n₁ ⊗ (ι n₂ ⊗ ι n₃)}) ∙ ♭ ∙ recursive-transposeᵣ))

{-
`ffti : NonZeroₛ s → Inp (ar (ι 2 ⊗ s) R) (ar (ι 2 ⊗ s) R)
`ffti (ι nz) = dft nz
`ffti (_⊗_ {p = p} nzs nzp) =
  part (`ffti nzs) (bothᵣ idh (left idh)) 
  >>> twid ⦃ nzs ⊗ nzp ⦄
  >>> part (`ffti nzp) (bothᵣ idh (right idh)) 
  -->>> ? --copy (eq ⊕ (♯ ∙ reindex (*-comm (size p) _) ∙ ♭ ∙ swap)) 
-}
  

`ffts : ∀ { V } → Stmt V (ar (ι 2 ⊗ s) R)
`ffts {ι n} = dft
`ffts {s ⊗ p} = view (nest ∙ resh (swap ∙ assoᵣ)) (pfor (λ _ → `ffts {s})) 
                >>> twid
                >>> view (nest ∙ resh (swap ∙ assoᵣ ∙ eq ⊕ swap)) (pfor (λ i → `ffts {p}))
                >>> copy λ t → pfor λ i → (write (sel (var t) 
                                (ixr (var i) (eq ⊕ (♯ ∙ reindex (*-comm (size p) _) ∙ ♭ ∙ swap)))))

`transpose-test₁ : Inp (ar s R) (ar (s ᵗ) R)
`transpose-test₁ {s} = copy (recursive-transposeᵣ)

module Interp (real : Real) (cplx : Cplx) where
  open Cplx cplx renaming (_+_ to _+𝕔_; _*_ to _*𝕔_)
  open Real.Real real using (_ᵣ; ℝ)
  
  open import Matrix.Equality
  open import Matrix.Reshape
  open import FFT cplx using (twiddles; offset-prod; FFT′; FFT′′)
--  open import Proof cplx

  Sem : Ty → Set
  Sem R = ℝ
  Sem C = ℂ
  Sem (ix x) = Position x
  Sem (τ ⇒ σ) = Sem τ → Sem σ

  -- With the current state of Complex, the below cannot be defined without giving
  -- a concrete definition, this will make interp-inp... challenging
  --ℝ-to-ℂ : Ar (ι 2 ⊗ s) ℝ → Ar s ℂ
  --ℝ-to-ℂ ar i = ?

  --interp-inp : Inp τ σ → Sem τ → Sem σ
  --interp-inp (dft nz) ar = ? -- λ p → interp (`dft ⦃ nz ⦄ `$ (` ar) `$ (` p))
  --interp-inp (twid {s} {p} ⦃ nz-s⊗p ⦄ ) ar = ? --zipWith _*𝕔_ ar (twiddles ⦃ nz-s⊗p ⦄)
  ----interp-inp (part-col inp eq) = ? --reshape swap ∘ unnest ∘ map (interp-inp inp) ∘ nest ∘ reshape swap 
  ----interp-inp (part-row inp eq) = ? --               unnest ∘ map (interp-inp inp) ∘ nest
  --interp-inp (inp₁ >>> inp₂) = interp-inp inp₂ ∘ interp-inp inp₁
  --interp-inp (copy rshp) = reshape rshp


  --prf : (nz-s : NonZeroₛ s) → (ar : Ar s ℂ) → (interp-inp (`ffti nz-s)) ar ≡ reshape m♭ (FFT′ ⦃ nz-s ⦄ ar)

module ShowC where
  open import Data.Nat
  open import Data.String hiding (show)
  open import Data.Product hiding (swap)
  open import Data.Maybe hiding (_>>=_)
  open import Data.Empty
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

  component-ix : Component → Ix (ι 2)
  component-ix REAL = ι "0"
  component-ix IMAG = ι "1"

  component-sym : Component → String
  component-sym REAL = "r"
  component-sym IMAG = "i"

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

  iota : Ix (ι n) → String
  iota (ι x) = x

  offset-prod : Ix s → String
  offset-prod (ι x) = x
  offset-prod {s ⊗ p} (i ⊗ j) = printf "(%s * %s)" (offset i) (offset j)

  for-template : String → ℕ → String → String
  for-template i n expr = printf "for (size_t %s = 0; %s < %u; %s++) {\n%s\n}" i i n i expr

  real-type : String
  real-type = "real "

  complex-type : String
  complex-type = "complex " ++ real-type

  malloc-op : (type : String) → Shape → String
  malloc-op ty s = printf "malloc(%u * sizeof(%s))" (size s) ty

  calloc-op : (type : String) → Shape → String
  calloc-op ty s = printf "calloc(%u, sizeof(%s))" (size s) ty

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

  loop-nest : (s : Shape) → Ix s → (String → String)
  loop-nest (ι n    ) (ι i    ) = for-template i n
  loop-nest (sₗ ⊗ sᵣ) (iₗ ⊗ iᵣ) = loop-nest sₗ iₗ ∘ loop-nest sᵣ iᵣ

  shape-helper : Shape → String
  shape-helper (ι n)   = printf "[%u]" n
  shape-helper (s ⊗ p) = shape-helper s ++ shape-helper p

  rshp-ix : Reshape s p → Ix s → Ix p
  rshp-ix eq i = i
  rshp-ix (rshp₁ ∙ rshp₂) i = rshp-ix rshp₁ $ rshp-ix rshp₂ i
  rshp-ix (rshp₁ ⊕ rshp₂) (i₁ ⊗ i₂) = rshp-ix rshp₁ i₁ ⊗ rshp-ix rshp₂ i₂
  rshp-ix (split {m} {n}) (ι x) = ι (printf "(%s / %u)" x n) ⊗ ι (printf "(%s %% %u)" x n)
  rshp-ix (flat {m} {n}) (ι x₁ ⊗ ι x₂) = ι (printf "((%s * %u) + %s)" x₁ n x₂)
  rshp-ix Reshape.swap (i₁ ⊗ i₂) = i₂ ⊗ i₁
  rshp-ix assoₗ ((i ⊗ j) ⊗ k) = i ⊗ (j ⊗ k)
  rshp-ix assoᵣ (i ⊗ (j ⊗ k)) = (i ⊗ j) ⊗ k

  -- Have to be careful here because, assuming an input shape of s ⊗ p, in the inp definition of 
  -- ufft I do not swap and so call pretwid over the shape s ⊗ p, while in the agda definition of prefft
  -- We call pre-twid over p ⊗ s!
  preoffset-prod : Ix (s ⊗ p) → String
  preoffset-prod {s} {p} (i ⊗ j) = printf "(%s * %s)" (iota (rshp-ix (♭ ∙ recursive-transposeᵣ) i)) (iota (rshp-ix (♭ ) j))
  --preoffset-prod {s} {p} (i ⊗ j) = printf "(%s * %s)" (offset (i)) (offset (rshp-ix (recursive-transposeᵣ) j))
  --preoffset-prod {s} {p} (i ⊗ j) = printf "(%s * %s)" (offset (rshp-ix recursive-transposeᵣ i)) (offset (j))
  --preoffset-prod {s} {p} (i ⊗ j) = printf "(%s * %s)" (iota (rshp-ix (♭) i)) (iota (rshp-ix (♭ ∙ recursive-transposeᵣ) j))
  
  data Sel : Shape → Shape → Set where
    idh   : Sel s s
    view  : Sel s p → Reshape q s → Sel q p
    chain : Sel s p → Sel p q → Sel s q
    left  : Ix p → Sel q s → Sel q (s ⊗ p)
    right : Ix s → Sel q p → Sel q (s ⊗ p)
    bothₗ : Sel q₁ p → Sel q₂ s → Sel (q₁ ⊗ q₂) (p ⊗ s)
    --bothᵣ : Sel q₁ s → Sel q₂ p → Sel (q₁ ⊗ q₂) (p ⊗ s)

  data AR : Ty → Set where
    --cst : String → AR C
    rst : String → AR R
    arr : String → Sel p s → AR (ar p R)

  ix-up : Sel s p → Ix s → Ix p
  ix-up idh i = i
  ix-up (view se x)    i = ix-up se (rshp-ix x i)
  ix-up (chain se se₁) i = ix-up se₁ (ix-up se i)
  ix-up (left x se)    i = ix-up se i ⊗ x
  ix-up (right x se)   i = x ⊗ ix-up se i
  ix-up (bothₗ x y) (i ⊗ j) = ix-up x i ⊗ ix-up y j
  --ix-up (bothᵣ x y) (i ⊗ j) = ix-up y j ⊗ ix-up x i

  to-sel′ : Ix s → String → String
  to-sel′ i a = printf "%s%s" a $ ix-join (ix-map (printf "[%s]") i) ""
    where
      ix-join : Ix s → (d : String) → String
      ix-join (ι x) d = x
      ix-join (i ⊗ j) d = ix-join i d ++ d ++ ix-join j d
      
      ix-map : (String → String) → Ix s → Ix s
      ix-map f (ι x) = ι (f x)
      ix-map f (i ⊗ j) = ix-map f i ⊗ ix-map f j

  to-sel : Ix s → String → String
  to-sel i a = to-sel′ i (printf "(*%s)" a)

  sel-to-str : String → Sel s p → Ix s → String
  sel-to-str ptr se ixs = to-sel (ix-up se ixs) ptr


  ⊂-to-sel : (s⊂p : s ⊂ p) → State ℕ ((Ix (inv-⊂ s⊂p)) × Sel s p)

  ⊂-to-sel (left {s₂ = s₂} idh) = do
    i ← generateIx s₂
    return (i , left i idh)
  ⊂-to-sel (left {s₂ = s₂} (srt x))  = do
    i ← generateIx s₂
    j , se ← ⊂-to-sel x
    return ( (j ⊗ i) , left i se)
  ⊂-to-sel (right {s₁ = s₁} idh)     = do
    i ← generateIx s₁
    return (i , right i idh)
  ⊂-to-sel (right {s₁ = s₁} (srt x)) = do
    i ← generateIx s₁
    j , se ← ⊂-to-sel x
    return ((i ⊗ j) , right i se)
  ⊂-to-sel (bothₗ a idh)     = do
    i , seᵢ ← ⊂-to-sel a
    return (i , bothₗ seᵢ idh)
  ⊂-to-sel (bothₗ a (srt x)) = do
    i , seᵢ ← ⊂-to-sel a
    j , seⱼ ← ⊂-to-sel x
    return ((i ⊗ j) , bothₗ seᵢ seⱼ)
  ⊂-to-sel (bothᵣ idh a)     = do
    j , seⱼ ← ⊂-to-sel a
    return (j , bothₗ idh seⱼ)
  ⊂-to-sel (bothᵣ (srt x) a) = do
    i , seᵢ ← ⊂-to-sel x
    j , seⱼ ← ⊂-to-sel a
    return ((i ⊗ j) , bothₗ seᵢ seⱼ)

  create-tmp-mem : (type : String) → Sel s p → (Shape → String) → State ℕ (String × String)
  create-tmp-mem {s} ty _ op = do
    tmp-var ← fresh-var
    let declaration = printf "%s (*%s)%s = %s;" ty tmp-var (shape-helper s) (op s)
    return $ tmp-var , declaration

  create-hole-copy : (type : String) → String → Sel s p → State ℕ (String × String)
  create-hole-copy {s} ty ptr se = do
    tmp-var , var-declaration ← create-tmp-mem ty se (malloc-op ty)
    i ← generateIx s
    let copy-values = loop-nest s i $ printf "%s = %s;" (to-sel i tmp-var) (sel-to-str ptr se i)
    return $ tmp-var , var-declaration ++ copy-values

  copy-into-sel : (fromPtr : String) → (toPtr : String) → Sel s p → State ℕ String
  copy-into-sel {s} fromPtr toPtr se = do
    i ← generateIx s
    return $ loop-nest s i $ printf "%s = %s;" (sel-to-str toPtr se i) (to-sel i fromPtr)

  --for-template : String → ℕ → String → String
  --for-template i n expr = printf "for (size_t %s = 0; %s < %u; %s++) {\n%s\n}" i i n i expr

  ----- TODO: Change this such that a subshape ι n ⊂ s can be used to select 
  ----- which loop to vectorise over.... maybe

  -- This needs to do the actuall looping

  ⊂-preserves-SIMD : ?SIMD s → p ⊂ s → ?SIMD p
  ⊆-preserves-SIMD : ?SIMD s → p ⊆ s → ?SIMD p

  ⊂-preserves-SIMD {s₁ ⊗ s₂} (SIMD-s₁ ⊗ SIMD-s₂) (left  p⊆s₁) = ⊆-preserves-SIMD SIMD-s₁ p⊆s₁
  ⊂-preserves-SIMD {s₁ ⊗ s₂} (SIMD-s₁ ⊗ SIMD-s₂) (right p⊆s₂) = ⊆-preserves-SIMD SIMD-s₂ p⊆s₂
  ⊂-preserves-SIMD {s₁ ⊗ s₂} (SIMD-s₁ ⊗ SIMD-s₂) (bothₗ q₁⊂s₁ q₂⊆s₂) = ⊂-preserves-SIMD SIMD-s₁ q₁⊂s₁ ⊗ ⊆-preserves-SIMD SIMD-s₂ q₂⊆s₂
  ⊂-preserves-SIMD {s₁ ⊗ s₂} (SIMD-s₁ ⊗ SIMD-s₂) (bothᵣ q₁⊆s₁ q₂⊂s₂) = ⊆-preserves-SIMD SIMD-s₁ q₁⊆s₁ ⊗ ⊂-preserves-SIMD SIMD-s₂ q₂⊂s₂

  ⊆-preserves-SIMD {ι _} (ι m) idh = ι m
  ⊆-preserves-SIMD (SIMD-s₁ ⊗ SIMD-s₂) idh = SIMD-s₁ ⊗ SIMD-s₂
  ⊆-preserves-SIMD (SIMD-s₁ ⊗ SIMD-s₂) (srt p⊂s) = ⊂-preserves-SIMD (SIMD-s₁ ⊗ SIMD-s₂) p⊂s


  -- combine-⊆ cannot be defined (easily) as inv-⊆ is not guaruteed to exist, show
  -- I ended up with this ugly mess
  combine-⊂ : (p⊂s : p ⊂ s) → Ix p → Ix (inv-⊂ p⊂s) → Ix s
  combine-⊂ (left idh) ix-p ix-p′ = ix-p ⊗ ix-p′
  combine-⊂ (left (srt p⊂s₁)) ix-p (ix-p′ ⊗ ix-s₁) = combine-⊂ p⊂s₁ ix-p ix-p′ ⊗ ix-s₁
  combine-⊂ (right idh) ix-p ix-p′ = ix-p′ ⊗ ix-p
  combine-⊂ (right (srt p⊂s₂)) ix-p (ix-s₁ ⊗ ix-p′) = ix-s₁ ⊗ combine-⊂ p⊂s₂ ix-p ix-p′
  combine-⊂ (bothₗ q₁⊂s₁ idh) (ix-q₁ ⊗ ix-q₂) ix-q₁′ = combine-⊂ q₁⊂s₁ ix-q₁ ix-q₁′ ⊗ ix-q₂
  combine-⊂ (bothₗ q₁⊂s₁ (srt q₂⊂s₂)) (ix-q₁ ⊗ ix-q₂) (ix-q₁′ ⊗ ix-q₂′) = combine-⊂ q₁⊂s₁ ix-q₁ ix-q₁′ ⊗ combine-⊂ q₂⊂s₂ ix-q₂ ix-q₂′
  combine-⊂ (bothᵣ idh q₂⊂s₂) (ix-q₁ ⊗ ix-q₂) ix-q₁′ = ix-q₁ ⊗ combine-⊂ q₂⊂s₂ ix-q₂ ix-q₁′
  combine-⊂ (bothᵣ (srt q₁⊂s₁) q₂⊂s₂) (ix-q₁ ⊗ ix-q₂) (ix-q₁′ ⊗ ix-q₂′) = combine-⊂ q₁⊂s₁ ix-q₁ ix-q₁′ ⊗ combine-⊂ q₂⊂s₂ ix-q₂ ix-q₂′

  --tmp {.(ι (m * LANES))} {p} (ι m) = ?
  --tmp {s ⊗ s₁} m = ?

  right-most : Shape → ℕ
  right-most (ι n) = n
  right-most (_ ⊗ s) = right-most s

  right-most-sub : (s : Shape) → (ι (right-most s)) ⊆ s
  right-most-sub (ι n) = idh
  right-most-sub (s₁ ⊗ s₂) = srt (right (right-most-sub s₂))

  SIMD-pragma : String
  SIMD-pragma = "\n#pragma omp simd\n"

{-

  SIMD-loop′ : ?SIMD s → (Ix s → String) → (ι (right-most s)) ⊆ s → ?SIMD (ι (right-most s)) → State ℕ String
  SIMD-loop′ {s} SIMD-s f ιn⊆s SIMD-ιn with right-most s -- This with is needed to be able to admit the absurd case
  SIMD-loop′ {.(ι (m * LANES))} (ι m) f idh SIMD-ιn | .(m * LANES) = do
    -- In this case we don't need to copy out, as the data is already vecotorised
    i ← generateIx (ι m)
    a ← generateIx (ι LANES)
    let j = rshp-ix flat (i ⊗  a)
    return  (loop-nest (ι m) i
            $  SIMD-pragma
            ++ loop-nest (ι LANES) a (f j))
  SIMD-loop′ {s₁ ⊗ s₂} (SIMD-s₁ ⊗ SIMD-s₂) f (srt ιn⊂s) (ι m) | _ with inv-⊂ ιn⊂s
  SIMD-loop′ {s₁ ⊗ s₂} (SIMD-s₁ ⊗ SIMD-s₂) f (srt ιn⊂s) (ι m) | _ | s′ = do
    ix-s′ ← generateIx (inv-⊂ ιn⊂s)
    
    ix-m ← generateIx (ι m)
    ix-lanes ← generateIx (ι LANES)
    -- This hole is the point at which I can no longer use inp, as I'm not parsing enough information

    let tmp = combine-⊂ ιn⊂s (rshp-ix flat (ix-m ⊗ ix-lanes)) ix-s′
    return (f ?) 

-}
  --SIMD-loop′ {ι x} SIMD-s f ιn⊆s (ι m) | n@.(m * LANES) | nothing = ?
  --SIMD-loop′ {s ⊗ s₁} (SIMD-s ⊗ SIMD-s₁) f (srt (left x)) (ι m) | n@.(m * LANES) | nothing = ?
  --SIMD-loop′ {s ⊗ s₁} (SIMD-s ⊗ SIMD-s₁) f (srt (right x)) (ι m) | n@.(m * LANES) | nothing = ?

  -- This case is invalid, but is a pain to find a ⊥ case for
  --do 
  --SIMD-loop′ {s} SIMD-s f ιn⊆s (ι m) | n@.(m * LANES) | just x = do
  --  --- Create temp array
  --  working-mem ← fresh-var
  --  let assign-mem = printf "(*%s)[%u][%u] = malloc(sizeof *%s);" working-mem m LANES working-mem

  --  let outer-loop = loop-nest 
  --  
  --  --- Copy into tmp array
  --  --- SIMD loop
  --  --- Copy out of tmp array
  --  ?

  {-
  -- This needs to create and then free the temp memory
  SIMD-loop : ?SIMD s → (Ix s → String) → State ℕ String
  SIMD-loop {s} SIMD-s f = do
    -- P will always be (ι n), annoyingly however we don't carry this property
    let p = right-most s
    let p⊆s = right-most-sub s
    let SIMD-p = ⊆-preserves-SIMD SIMD-s p⊆s

    SIMD-loop′ SIMD-s f p⊆s SIMD-p
  -}

  SIMD-loop-new′ : 
      ?SIMD s 
    → (elemAccessor : Ix (ι 2 ⊗ s) → String) 
    → (operation : (Ix (s) × (Ix (ι 2) → String)) → String) 
    → (ι (right-most s)) ⊆ s 
    → ?SIMD (ι (right-most s)) 
    → State ℕ String
  SIMD-loop-new′ {s} SIMD-s _ _ _ _ with right-most s
  SIMD-loop-new′ {.(ι (m * LANES))} (ι m) e f idh SIMD-ιn | .(m * LANES) = do
    i ← generateIx (ι m)
    j ← generateIx (ι LANES)
    let i⊗j = rshp-ix flat (i ⊗ j)

    return  $ loop-nest (ι m) i 
            $  SIMD-pragma
            ++ loop-nest (ι LANES) j 
            (  f (i⊗j , λ c → e (c ⊗ i⊗j)))
            
  SIMD-loop-new′ {s₁ ⊗ s₂} (SIMD-s₁ ⊗ SIMD-s₂) e f (srt ιn⊂s) (ι m) | _ = do
    ix-s′ ← generateIx (inv-⊂ ιn⊂s)
    
    ix-ι2 ← generateIx (ι 2)
    ix-m ← generateIx (ι m)
    ix-lanes ← generateIx (ι LANES)
    let ix-ml♭ = ix-ι2 ⊗ (rshp-ix flat (ix-m ⊗ ix-lanes))

    -- Another place where INP really isn't descriptive enough (or I just haven't
    -- parsed enough info, as we cannot infer real from anywhere so just have to
    -- piss it into existence and pray)
    working-mem ← fresh-var
    let malloc-mem = printf "%s (*%s)%s = %s;" 
                      real-type 
                      working-mem
                      (shape-helper (ι 2 ⊗ ι (size (ι m ⊗ ι LANES))))
                      (malloc-op real-type (ι 2 ⊗ (ι m ⊗ ι LANES)))
    let accessor = combine-⊂ ιn⊂s (rshp-ix flat (ix-m ⊗ ix-lanes)) ix-s′

    -- As I wrote the below funciton, I felt small parts of my soul die, this is in dire need of improvement
    let outer-loop = loop-nest (inv-⊂ ιn⊂s) ix-s′ (
                        -- Copy into working-mem
                           (loop-nest (ι 2) ix-ι2
                             (loop-nest (ι m) ix-m 
                              (loop-nest (ι LANES) ix-lanes (
                                printf "%s = %s;" (to-sel ix-ml♭ working-mem) (e (ix-ι2 ⊗ accessor))
                              ))
                             )
                           )
                        -- perform operations in simd loop
                        ++ (loop-nest (ι m) ix-m 
                            (SIMD-pragma  ++ loop-nest (ι LANES) ix-lanes (
                              printf "%s" (f (accessor , λ c → to-sel (c ⊗ rshp-ix flat (ix-m ⊗ ix-lanes)) working-mem))
                            ))
                           )
                        -- Copy back
                        ++ (loop-nest (ι 2) ix-ι2
                             (loop-nest (ι m) ix-m 
                              (loop-nest (ι LANES) ix-lanes (
                                printf "%s = %s;" (e (ix-ι2 ⊗ accessor)) (to-sel ix-ml♭ working-mem)
                              ))
                             )
                           )
                      )


    --(f (accessor , (λ c → e (c ⊗ accessor)))) 
    return $ malloc-mem ++ outer-loop

  SIMD-loop-new : ?SIMD s → (elemAccessor : Ix (ι 2 ⊗ s) → String) → (operation : (Ix (s) × (Ix (ι 2) → String)) → String) → State ℕ String
  SIMD-loop-new {s} SIMD-s e f = do
    let p = right-most s
    let p⊆s = right-most-sub s
    let SIMD-p = ⊆-preserves-SIMD SIMD-s p⊆s
    
    SIMD-loop-new′ SIMD-s e f p⊆s SIMD-p
    {-
      Copy into sequential memory
      Perform operations
      Copy back
    -}
    --i ← generateIx ?
    --?
    

  -- This is the old SIMD-loop, The above code includes attempts at creating a 
  -- better one, however I think I have ran into the limmitations of Inp here, as
  -- I need to sepearate what elements are accessed and what opearations are performed

  
  SIMD-loop : ?SIMD s → (Ix s → String) → State ℕ String
  SIMD-loop {.(ι (m * LANES))} (ι m) f = do
    {-
      Copy into sequential memory
      Perform operations
      Copy back
    -}
    i ← generateIx (ι m)
    a ← generateIx (ι LANES)
    let j = rshp-ix flat (i ⊗  a)
    return  $  loop-nest (ι m) i
            $  "\n#pragma omp simd\n" 
            ++ loop-nest (ι LANES) a (f j)
  SIMD-loop {(s₁ ⊗ s₂)} (_ ⊗ pred₂) f = do
    i ← generateIx s₁
    inner ← SIMD-loop pred₂ λ j → f (i ⊗ j)
    return $ loop-nest s₁ i inner

  use-dft-macro : ℕ → String → String → String
  use-dft-macro n xs ys = printf "SPLIT_DFT(%u, ((real (*)[%u])%s), ((real (*)[%u])%s));" n n xs n ys

  minus-omega : Component → (n : ℕ) → (j : String) → String
  minus-omega = printf "minus_omega_%s(%u, %s)" ∘ component-sym 

  to-vali : Inp τ σ → AR τ → State ℕ (String × AR σ)
  to-vali (dft {n} nz-n) (arr ptr se) = do 
    inp-var , create-inp-mem  ← create-hole-copy real-type ptr se
    out-var , declare-out-mem ← create-tmp-mem real-type se (calloc-op real-type)
    let use-dft = use-dft-macro n inp-var out-var
    copy-out-to-ptr ← copy-into-sel out-var ptr se
    return $ (create-inp-mem ++ declare-out-mem ++ use-dft ++ copy-out-to-ptr) , arr ptr se
  to-vali (twid {s} {p}) (arr ptr se) = do
    i ← generateIx (s ⊗ p)
    ----- I Really wish I had fin types here....
    let memSel_r = sel-to-str ptr se ((component-ix REAL) ⊗ i)
    let memSel_i = sel-to-str ptr se ((component-ix IMAG) ⊗ i)
    
    tmp-var ← fresh-var
    let init-tmp-var = printf "%s %s;\n" real-type tmp-var

    let power = offset-prod i
    let size-sp = size s * size p
    let ops =  (printf "%s = %s;\n" tmp-var memSel_r)
            ++ (printf 
                  "%s = (%s * %s) - (%s * %s);\n" 
                  memSel_r 
                  memSel_r 
                  (minus-omega REAL size-sp power)
                  memSel_i
                  (minus-omega IMAG size-sp power)
               )
            ++ (printf 
                  "%s = (%s * %s) + (%s * %s);\n" 
                  memSel_i 
                  tmp-var
                  (minus-omega IMAG size-sp power)
                  memSel_i
                  (minus-omega REAL size-sp power)
               )
    
    return $ (init-tmp-var ++ loop-nest (s ⊗ p) i ops , arr ptr se)
  to-vali (pretwid {s} {p} pred) (arr ptr se) = do

    tmp-var ← fresh-var
    let init-tmp-var = printf "%s %s;\n" real-type tmp-var

    let size-sp = size s * size p

    simd-loop′ ← SIMD-loop-new pred (sel-to-str ptr se) λ { 
        ((ix-s) , val) → 
            (printf "%s = %s;\n" tmp-var (val (component-ix REAL)))
            ++ (printf 
                  "%s = (%s * %s) - (%s * %s);\n" 
                  (val (component-ix REAL))
                  (val (component-ix REAL))
                  (minus-omega REAL size-sp (preoffset-prod ix-s))
                  (val (component-ix IMAG))
                  (minus-omega IMAG size-sp (preoffset-prod ix-s))
               )
            ++ (printf 
                  "%s = (%s * %s) + (%s * %s);\n" 
                  (val (component-ix IMAG))
                  tmp-var
                  (minus-omega IMAG size-sp (preoffset-prod ix-s))
                  (val (component-ix IMAG))
                  (minus-omega REAL size-sp (preoffset-prod ix-s))
               )
      }

    simd-loop ← SIMD-loop pred λ i →
               (printf "%s = %s;\n" tmp-var (sel-to-str ptr se ((component-ix REAL) ⊗ i)))
            ++ (printf 
                  "%s = (%s * %s) - (%s * %s);\n" 
                  (sel-to-str ptr se ((component-ix REAL) ⊗ i)) 
                  (sel-to-str ptr se ((component-ix REAL) ⊗ i)) 
                  (minus-omega REAL size-sp (preoffset-prod i))
                  (sel-to-str ptr se ((component-ix IMAG) ⊗ i))
                  (minus-omega IMAG size-sp (preoffset-prod i))
               )
            ++ (printf 
                  "%s = (%s * %s) + (%s * %s);\n" 
                  (sel-to-str ptr se ((component-ix IMAG) ⊗ i)) 
                  tmp-var
                  (minus-omega IMAG size-sp (preoffset-prod i))
                  (sel-to-str ptr se ((component-ix IMAG) ⊗ i))
                  (minus-omega REAL size-sp (preoffset-prod i))
               )
    
    return (init-tmp-var ++ simd-loop′ , arr ptr se)
    --return $ (init-tmp-var ++ loop-nest (s ⊗ p) i ops , arr ptr se)
  to-vali (part {s} {p = p} e s⊆p ) (arr {s = t} ptr se) = 
    do
      i , s-sel ← ⊂-to-sel s⊆p
      expr , _ ← to-vali e (arr ptr (chain (s-sel) se))
      return $ (loop-nest (inv-⊂ s⊆p) i expr) , arr ptr se
  to-vali {τ} (inp₁ >>> inp₂) arτ = do
    e₁ , ARδ ← to-vali inp₁ arτ
    e₂ , ARσ ← to-vali inp₂ ARδ
    return $ (e₁ ++ e₂) , ARσ
  to-vali (copy {s = s} {p = p} rshp) (arr ptr se) = do

    ------ working-mem , copy-out ← create-hole-copy ptr se
    working-mem ← fresh-var
    let var-declaration = printf "%s (*%s)%s = %s;" 
                            real-type
                            working-mem
                            (shape-helper (ι (size s))) 
                            (malloc-op real-type (ι (size s))) --TODO : This is not reliable with real-type put here
    --working-mem , var-declaration ← create-tmp-mem se malloc-op
    i ← generateIx s
    let copy-values = loop-nest s i $ 
                        printf "%s = %s;" 
                          (to-sel (rshp-ix (♭ ∙ rshp) i) working-mem) 
                          (sel-to-str ptr se i)
    let copy-out = var-declaration ++ copy-values
    ------ return $ var , var-declaration ++ copy-values

    j ← generateIx s
    let copy-in = loop-nest s j $ 
                    printf "%s = %s;" 
                      (sel-to-str ptr se j) 
                      (to-sel (rshp-ix ♭ j) working-mem)

    return $ copy-out ++ copy-in , arr ptr idh

  num-type : Num τ → String
  num-type C = complex-type
  num-type R = real-type
  num-type {ix s ⇒ τ} (arr x) = num-type {τ} x ++ (shape-helper s)
  
  final-type : Fut τ → String
  final-type (num x) = num-type x
  final-type (fun x fut) = final-type fut
  
  parameter-list-app : Fut τ → String → String
  parameter-list-app (num x)    pre = pre
  parameter-list-app (fun x next) pre = parameter-list-app next (printf "%s , %s" pre (num-type x))

  shape-to-arg : Shape → String → String
  shape-to-arg (ι n)   res = printf "(*%s)[%u]" res n
  shape-to-arg (s ⊗ p) res = shape-to-arg s res ++ shape-helper p

  ty-to-arg : Fut τ → String → String
  ty-to-arg {C}        (num x)       res = printf "%s (*%s)" complex-type res
  ty-to-arg {R}        (num x)       res = printf "%s (*%s)" real-type    res
  ty-to-arg {ix s ⇒ R} (num (arr R)) res = real-type    ++ shape-to-arg s res 
  ty-to-arg {ix s ⇒ C} (num (arr C)) res = complex-type ++ shape-to-arg s res
  ty-to-arg {ix s ⇒ (ix p ⇒  τ)} (num (arr (arr x))) res = ty-to-arg {ix p ⇒ τ} (num (arr x)) res ++ shape-helper s
  -- The below case is the one I have been struggling to work out how to deal with...
  ty-to-arg {τ ⇒ σ} (fun x fut) res = printf "%s (*%s) (%s)" (final-type fut) res (parameter-list-app fut (num-type x))

  AR-name : AR τ → String
  AR-name (rst name  ) = name
  AR-name (arr name _) = name

  show′ : Fut τ → (AR τ) → (Inp τ σ) → String → String × String
  show′ fut ARτ e fName = runState (
      do
        let arg = ty-to-arg fut $ AR-name ARτ
        val , mem ← to-vali e ARτ
        return $ (printf "void %s(%s) { %s }\n" fName arg val) , (printf "void %s(%s);\n" fName arg)
    ) 0 .proj₂


module Tests where
  open import Data.Empty
  open import Relation.Nullary
  open import Data.String hiding (show)
  open import Agda.Builtin.Unit using (tt)
  open import Data.Product hiding (swap)
  open import Text.Printf

  open ShowC

  sh : Shape
  sh = (ι 5 ⊗ ι 6) ⊗ ι 7

  sh-big : Shape
  sh-big = ((ι 5 ⊗ ι 7) ⊗ ι 8) ⊗ (ι 9 ⊗ ι 10)

  sh-mini : Shape
  sh-mini = ι 2 ⊗ (ι 3 ⊗ ι 3)

  {-
  fft-big : E V _
  fft-big = `fft {s = sh-big} ⦃ ((ι _ ⊗ ι _) ⊗ ι _) ⊗ (ι _ ⊗ ι _) ⦄
  
  fft-mini : E V _
  fft-mini = `fft {s = sh-mini} ⦃ ι _ ⊗ (ι _ ⊗ ι _) ⦄

  fft : (s : Shape) → ⦃ NonZeroₛ s ⦄ → E V _
  fft s = `fft {s = s}
  -}

  fft : (s : Shape) → ⦃ _ : NonZeroₛ s ⦄ → ?SIMD s → Inp _ _
  fft s ⦃ nz ⦄ = `ffti nz 

  --isNum : (τ : Ty) → Dec (Num τ)
  --isNum C = yes C
  --isNum (ix x) = no λ ()
  --isNum (C ⇒ σ) = no λ ()
  --isNum ((_ ⇒ _) ⇒ σ) = no λ ()
  --isNum (ix x ⇒ σ) with isNum σ
  --... | yes p = yes (arr p)
  --... | no ¬p = no λ { (arr p) → ¬p p }

  --isFut : (τ : Ty) → Dec (Fut τ)
  --isFut C = yes (num C)
  --isFut (ix x) = no λ { (num ()) }
  --isFut (C ⇒ σ) with isFut σ
  --... | no ¬p = no λ { (fun _ p) → ¬p p }
  --... | yes p = yes (fun C p) 
  --isFut (ix x ⇒ σ) with isNum σ
  --... | no ¬p = no λ { (num (arr p)) → ¬p p }
  --... | yes p = yes (num (arr p))
  --isFut (τ@(_ ⇒ _) ⇒ σ) with isNum τ
  --... | no ¬p = no λ { (fun p _) → ¬p p }
  --... | yes p with isFut σ
  --... | no ¬q = no λ { (fun _ q) → ¬q q }
  --... | yes q = yes (fun p q)

  preamble : String
  preamble = "#include <complex.h>\n" 
           ++ "#include <stddef.h>\n"
           ++ "#include <stdlib.h>\n"
           ++ "#include \"../src/minus-omega.h\"\n"
           ++ "#include \"../src/dft.h\"\n"
           ++ "\n"

  sizeDef : Shape → String → String
  sizeDef s name =     (printf "#ifndef %s_SIZE\n" name)
                    ++ (printf "#define %s_SIZE %u\n" name (size s))
                    ++ (printf "typedef real (*%s_TYPE)%s;\n" name (shape-helper (ι 2 ⊗ s)))
                    ++ "#endif\n"


  gen-fft : (s : Shape) → ⦃ _ : NonZeroₛ s ⦄ → ?SIMD s → String × String
  gen-fft s pred with show′ (num (arr R)) (arr "inp" idh) (fft s pred) "fft"
  ... | body , header = (preamble ++ (sizeDef s "fft") ++ header) , (preamble ++ (sizeDef s "fft") ++ body)

  gen-ufft : (s : Shape) → ⦃ _ : NonZeroₛ s ⦄ → ?SIMD s → String × String
  gen-ufft s ⦃ nz-s ⦄ pred with show′ (num (arr R)) (arr "inp" idh) (`uffti nz-s pred) "ufft"
  ... | body , header = (preamble ++ (sizeDef s "ufft") ++ header) , (preamble ++ (sizeDef s "ufft") ++ body)

  gen-fft-cube : ⦃ _ : NonZero n₁ ⦄ → ⦃ _ : NonZero n₂ ⦄ → ⦃ _ : NonZero n₃ ⦄ → String × String
  gen-fft-cube ⦃ nz-n₁ ⦄ ⦃ nz-n₂ ⦄ ⦃ nz-n₃ ⦄ with show′ (num (arr R)) (arr "inp" idh) (`fftCube nz-n₁ nz-n₂ nz-n₃ ) "fftCube"
  ... | body , header = (preamble ++ header) , (preamble ++ body)

  gen-transpose-test : (s : Shape) → String × String
  gen-transpose-test s with show′ (num (arr R)) (arr "inp" idh) (`transpose-test₁ {s}) "transposeTest"
  ... | body , header = (preamble ++ header) , (preamble ++ body)


open Tests using (gen-fft; gen-ufft; gen-fft-cube; gen-transpose-test) public
