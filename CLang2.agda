{-# OPTIONS --backtracking-instance-search #-}
{-# OPTIONS --instance-search-depth 10 #-}
{-# OPTIONS --guardedness #-}

module CLang2 where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties using (*-comm)
open import Data.Fin using (Fin; zero; suc; cast; toℕ)
open import Data.Product hiding (swap)
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

--infixr 5 _⇒_
--data Ty : Set where
--  C   : Ty
--  R   : Ty
--  ix  : Shape → Ty
--  _⇒_ : Ty → Ty → Ty

data Ty : Set where
  R : Ty
  ar : Shape → Ty → Ty
  ix : Shape → Ty

-- ar : Shape → Ty → Ty
-- ar s X = ix s ⇒ X

data Component : Set where
  REAL : Component
  IMAG : Component

variable
  τ σ δ ψ : Ty

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

data Stmt (V : Ty → Set) : Ty → Set

C : Ty
C = ar (ι 2) R

--{-# DISPLAY ar (Shape.ι 2) R = C #-}

data Copyable : Ty → Set where
  ℝ : Copyable R
  ℂ : Copyable (ar (ι 2) R)

data Exp (V : Ty → Set) : Ty → Set where
  var : V τ → Exp V τ
  ixr : Exp V (ix s) → Reshape p s → Exp V (ix p)
  sel : Exp V (ar s τ) → Exp V (ix s) → Exp V τ
  _𝕔*_ : Exp V C → Exp V C → Exp V C
  ω : Exp V (ix (s ⊗ p)) → Exp V C

data View (V : Ty → Set) : Ty → Ty → Set where
  nest   : View V (ar (s ⊗ p) τ)  (ar s (ar p τ))
  unnest : View V (ar s (ar p τ)) (ar (s ⊗ p) τ)
  vmap   : View V τ σ  → View V (ar s τ) (ar s σ)
  _∙_    : View V σ δ  → View V τ σ → View V τ δ
  resh   : Reshape s p → View V (ar s τ) (ar p τ)
  subs   : (p⊂s : p ⊂ s) → View V (ar s τ) (ar (inv-⊂ p⊂s) (ar p τ))

infixl 2 _>>>_
data Stmt V where
  dft  : ⦃ ?SIMD (ι n)   ⦄ → Stmt V (ar (ι 2 ⊗ ι n) R)
  twid : ⦃ ?SIMD (s ⊗ p) ⦄ → Stmt V (ar (ι 2 ⊗ (s ⊗ p)) R)

  write : Exp V τ → Stmt V τ

  view : View V τ σ → Stmt V σ → Stmt V τ

  pfor : (V (ix s) → Stmt V τ) → Stmt V (ar s τ)
  -- Would be nice to be more specific about the following, but gives map nicely
  -- which should be SIMD able without the need for copy (i.e. for the case where
  -- elements don't interact such as twiddle
  afor : Copyable τ → ((V τ × (V (ix s))) → Stmt V τ) → Stmt V (ar s τ)
  
  _>>>_ : Stmt V τ → Stmt V τ → Stmt V τ

  --copy : (V (ar s R) → Stmt V (ar s R)) → Stmt V (ar s R)

  -- Messy, vile, hate it
  --copy𝕣 : (V (ar s R) → Stmt V (ar s R)) → Stmt V (ar s R)
  --copy𝕔 : (V (ar s C) → Stmt V (ar s C)) → Stmt V (ar s C)
 
  copy : Copyable τ → (V (ar s τ) → Stmt V (ar s τ)) → Stmt V (ar s τ)

twid′ : ⦃ ?SIMD (s ⊗ p) ⦄ → ∀ {V} → Stmt V (ar (ι 2 ⊗ (s ⊗ p)) R)
twid′ {s} {p} = view (subs (left idh)) (
    afor ℂ (λ (v , i) → write (var v 𝕔* (ω (var i))))
  )
--twid′ {s} {p} = view (subs (left idh)) (copy ℂ λ t → pfor (λ i → write (
--    (sel (var t) (var i)) 𝕔* (ω (var i))
--  )))

--copy (λ t → view (subs (left idh)) (pfor (λ i → write (
--    (sel (var ?) (ixr (var i) ?)) 𝕔* ?
--  ))) )

--view (subs (left idh)) (copy (λ t → ?))

--(copy (λ t → (pfor (λ i → write (
--    (sel ? (var i)) 𝕔* ? ))
--  )))

ufft′ : ⦃ SIMD-s : ?SIMD s ⦄ → ∀{V} → Stmt V (ar (ι 2 ⊗ s) R)
ufft′ {ι n} = dft 
ufft′ {s₁ ⊗ s₂} ⦃ SIMD-s@(SIMD-s₁ ⊗ SIMD-s₂) ⦄ =
  view (subs (bothᵣ idh (left idh))) (pfor λ _ → ufft′ {s₁})
  >>> twid′
  >>> view (subs (bothᵣ idh (right idh))) (pfor λ _ → ufft′ {s₂})
  where instance
    --- I really don't think these should be necassary from reading the docs
    --- Doesn't even work with --backtracking-instance-search
    --- See my MRE for some playing arround with this, because it can also put 
    ---- agda into what appears to be a loop without a base case...
    _ : ?SIMD s₁
    _ = SIMD-s₁
    _ : ?SIMD s₂
    _ = SIMD-s₂

fft′ : ⦃ ?SIMD s ⦄ → ∀{V} → Stmt V (ar (ι 2 ⊗ s) R)
fft′ {s} ⦃ SIMD-s ⦄ = ufft′ ⦃ SIMD-s ⦄ >>> copy ℝ (λ t → pfor λ i → (write (
                    sel (var t) (ixr (var i) (eq ⊕ (♯ ∙ reindex (sym $ |s|≡|sᵗ| {s}) ∙ ♭ ∙ recursive-transposeᵣ)))
                 )))

--fft′ {ι n} = dft
--fft′ {s ⊗ p} = view (nest ∙ resh swap) (pfor (λ _ → fft′ {s})) 
--               >>> twid
--               >>> view nest (pfor (λ _ → fft′ {p}))
--               >>> copy (λ t → pfor λ i → (write (sel (var t) 
--                              (ixr (var i) (♯ ∙ reindex (*-comm (size p) _) ∙ ♭ ∙ swap)))))


module Codegen where
  open import Data.String as S
  open import Text.Printf
  open import Effect.Monad 
  open import Effect.Monad.State
  open RawMonadState {{...}}
  open RawMonad {{...}} hiding (_⊗_)
  instance
    _ = monad
    _ = monadState 


  data Ix : Shape → Set where
    ι : String → Ix (ι n)
    _⊗_ : Ix s → Ix p → Ix (s ⊗ p)

  combine-⊂ : (p⊂s : p ⊂ s) → Ix p → Ix (inv-⊂ p⊂s) → Ix s
  combine-⊂ (left idh) ix-p ix-p′ = ix-p ⊗ ix-p′
  combine-⊂ (left (srt p⊂s₁)) ix-p (ix-p′ ⊗ ix-s₁) = combine-⊂ p⊂s₁ ix-p ix-p′ ⊗ ix-s₁
  combine-⊂ (right idh) ix-p ix-p′ = ix-p′ ⊗ ix-p
  combine-⊂ (right (srt p⊂s₂)) ix-p (ix-s₁ ⊗ ix-p′) = ix-s₁ ⊗ combine-⊂ p⊂s₂ ix-p ix-p′
  combine-⊂ (bothₗ q₁⊂s₁ idh) (ix-q₁ ⊗ ix-q₂) ix-q₁′ = combine-⊂ q₁⊂s₁ ix-q₁ ix-q₁′ ⊗ ix-q₂
  combine-⊂ (bothₗ q₁⊂s₁ (srt q₂⊂s₂)) (ix-q₁ ⊗ ix-q₂) (ix-q₁′ ⊗ ix-q₂′) = combine-⊂ q₁⊂s₁ ix-q₁ ix-q₁′ ⊗ combine-⊂ q₂⊂s₂ ix-q₂ ix-q₂′
  combine-⊂ (bothᵣ idh q₂⊂s₂) (ix-q₁ ⊗ ix-q₂) ix-q₁′ = ix-q₁ ⊗ combine-⊂ q₂⊂s₂ ix-q₂ ix-q₁′
  combine-⊂ (bothᵣ (srt q₁⊂s₁) q₂⊂s₂) (ix-q₁ ⊗ ix-q₂) (ix-q₁′ ⊗ ix-q₂′) = combine-⊂ q₁⊂s₁ ix-q₁ ix-q₁′ ⊗ combine-⊂ q₂⊂s₂ ix-q₂ ix-q₂′

  freshv : String → State ℕ String
  freshv x = do
    n ← get
    modify suc
    return (printf "%s_%u" x n)

  new-ix : String → Ix s
  new-ix n = do
    proj₂ (runState (go n) 0) -- we can just number vars through
    where
      go : String → State ℕ (Ix s)
      go {ι x} n = do
        c ← get
        modify suc
        return (ι $′ printf "%s_%u" n c)
      go {s ⊗ p} n = do
        l ← go {s} n
        r ← go {p} n
        return (l ⊗ r)
      
  fresh-ix : String → State ℕ (Ix s)
  fresh-ix s = new-ix <$> freshv s 

  dim : Shape → ℕ
  dim (ι _) = 1
  dim (s ⊗ p) = dim s + dim p

  offset : Ix s → String
  offset (ι x) = x
  offset {s ⊗ p} (i ⊗ j) = printf "((%u * %s) + %s)" (size p) (offset i) (offset j)

  ix-join : Ix s → (d : String) → String
  ix-join (ι x) d = x
  ix-join (i ⊗ j) d = ix-join i d ++ d ++ ix-join j d

  ix-map : (String → String) → Ix s → Ix s
  ix-map f (ι x) = ι (f x)
  ix-map f (i ⊗ j) = ix-map f i ⊗ ix-map f j

  ix-fst : Ix (s ⊗ p) → Ix s
  ix-fst (i ⊗ j) = i

  ix-snd : Ix (s ⊗ p) → Ix p
  ix-snd (i ⊗ j) = j

  to-sel : Ix s → String → String
  to-sel i a = a ++ ix-join (ix-map (printf "[%s]") i) ""

  Val : Ty → Set 
  Val R = String
  Val (ar s τ) = Ix s → State ℕ (Val τ) -- TODO slice
  Val (ix s) = Ix s


  ix-reshape : Ix s → Reshape p s → Ix p 
  ix-reshape i eq = i
  ix-reshape i (r ∙ r₁) = ix-reshape (ix-reshape i r) r₁
  ix-reshape (i ⊗ i₁) (r ⊕ r₁) = ix-reshape i r ⊗ ix-reshape i₁ r₁
  ix-reshape (ι i ⊗ ι j) (split {n = n}) = ι (printf "(%s) * %u + (%s)" i n j)
  ix-reshape (ι i) (flat {n = n}) = ι (printf "(%s) / %u" i n)
                                  ⊗ ι (printf "(%s) %% %u" i n)
  ix-reshape (i ⊗ j) swap = j ⊗ i

  --omega : ℕ → Ix (s ⊗ p) → Val R
  --omega sz (i ⊗ j) = printf "minus_omega(%u, (%s * %s))" 
  --                           sz (offset (ix-reshape i (rev recursive-transposeᵣ))) (offset j)

  omega : ℕ → Ix (s ⊗ p) → Val C
  omega sz (i ⊗ j) (ι x) = return $ printf "minus_omega(%u, (%s * %s), %s)" sz (offset (ix-reshape i (rev recursive-transposeᵣ))) (offset j) x


  etov : Exp Val τ → State ℕ (Val τ)
  etov (var x) = return x
  etov (ixr e x) = do
    i ← etov e
    return (ix-reshape i x)
  etov (sel e e₁) = do
    a ← etov e
    i ← etov e₁
    a i
  etov (e₁ 𝕔* e₂) = do
    v₁ ← etov e₁
    v₂ ← etov e₂
    return λ i → do
      s₁_r ← v₁ (ι "0")
      s₁_i ← v₁ (ι "1")
      s₂_r ← v₂ (ι "0")
      s₂_i ← v₂ (ι "1")
      --ι 0 ≡ (s₁_r * s₁_r) - (s₁_i * s₂_i)
      --ι 1 ≡ (s₁_r * s₂_i) + (s₁_i * s₂_r)

      -- Here I am having a big problem, think I need to re-evaluate how I model pairs
      -- of reals away from how I did so in INP, as I need to be able to pattern match on i
      

      -- Maybe I try to change Ix?
      return $ printf "s₁ *𝕔 s₂; // where:\n//s₁_r = %s, s₁_i = %s, s₂_r = %s, s₂_i = %s\n" s₁_r s₁_i s₂_r s₂_i
  etov (ω {s} {p} j) = return λ c → do
    pos ← etov j
    omega (size (s ⊗ p)) pos c

  new-val : String → Val τ
  new-val {R} x = x
  -- note: ar 2 (ar 3 x) = λ i j → a[i][j], not a[j][i]
  new-val {ar s τ} n = λ i → return (new-val (to-sel i n))
  new-val {ix s} i = new-ix i

  fresh-val : String → State ℕ (Val τ)
  fresh-val s = new-val <$> freshv s

  valview : Val τ → View Val τ σ → State ℕ (Val σ)
  valview v nest = return λ i → return λ j → v (i ⊗ j)
  valview v unnest = return λ { (i ⊗ j) → do f ← v i ; f j}
  valview v (vmap α) = return λ i → do vi ← v i; valview vi α
  valview v (α ∙ β) = do
    w ← valview v β
    valview w α
  valview v (resh x) = return λ i → v (ix-reshape i x)
  valview v (subs p⊂s) = return λ i → return λ j → v (combine-⊂ p⊂s j i)

  for-loop : Ix s → String → String
  for-loop {ι n} (ι i) b = 
    printf "for (size_t %s = 0; %s < %u; %s++) { %s }"
            i i n i b
  for-loop {s ⊗ p} (i ⊗ j) b = for-loop i (for-loop j b)

  upd-ixs : Ix s → Ix s → String
  upd-ixs (ι i) (ι j) = printf "%s = %s;" i j
  upd-ixs (i ⊗ i′) (j ⊗ j′) = upd-ixs i j S.++ upd-ixs i′ j′

  vcopy : Val τ → Val τ → State ℕ String
  vcopy {R} v w = return (printf "%s = %s" v w)
  vcopy {ar x τ} v w = do
    i ← fresh-ix "i"
    vi ← v i
    wi ← w i
    b ← vcopy vi wi
    return (for-loop i b)
  vcopy {ix x} v w = return (upd-ixs v w)

  sizeof : Copyable τ → String
  sizeof ℝ = "sizeof(real)"
  sizeof ℂ = printf "(2 * %s)" (sizeof ℝ)

  tov : Val τ → Stmt Val τ → State ℕ String
  tov v (dft {n}) = do
    -- 99.99% wrong
    i ← freshv "i"
    j ← freshv "c"
    vi ← v (ι j ⊗ ι i)
    return (printf "DFT_SPLIT(%u, %s, %s, %s);" n i j vi)
  tov v (twid {s}{p}) = do
    i ← fresh-ix "i"
    vi ← v i
    return "DEPRECIATED"
    --let o = omega (size (s ⊗ p)) i
    --let b = printf "%s *= %s" vi o
    --return (for-loop i b)

  tov v (view α u) = do
    w ← valview v α
    tov w u

  tov v (pfor f) = do
    i ← fresh-ix "i"
    vi ← v i
    u ← tov vi (f i)
    return (for-loop i u)

  tov v (afor {s = s} ty f) = do
    i ← fresh-ix "i"
    vi ← v i
    u ← tov vi (f (vi , i))
    return (for-loop i u)

  tov v (write x) = do
    w ← etov x
    vcopy v w

  tov v (s >>> s₁) = do
    a ← tov v s
    b ← tov v s₁
    return (a S.++ b)

  tov v (copy {s = s} ty f) = do
    t ← freshv "t"
    let tv = new-val t
    let alloc = printf "%s = calloc(%u, %s);" t (size s) (sizeof ty)
    cpy ← vcopy tv v
    body ← tov v (f tv)
    let free = printf "free(%s);" t
    return (alloc S.++ cpy S.++ body S.++ free)

  comp : (∀ {V} → Stmt V τ) → (v : String) → State ℕ String
  comp v x = do
    w ← fresh-val x
    tov w v
  
  res = runState (comp (fft′ {s = ι 8 ⊗ ι 16} ⦃ ι 2 ⊗ ι 4 ⦄ ) "a") 0 .proj₂

  _ : res ≡ ?
  _ = ?


{-
#define DFT(__n, __i, __ei) \
  do { \
    cplx *__t = calloc(__n, sizeof(cplx)); \
    for (size_t __j = 0; __j < n; __j++) \
      __t[__j] = 0; \
    for (size_t __j = 0; __j < __n; __j++) \
      for (size_t __i = 0; __i < __n; __i++) \
        __t[__j] += (__ei * minus_omega(__n, (__j * __i))); \
  } while (0)

-}

{-
#define SPLIT_DFT(__n, __i, __component, __ei) \
  do { \
    ?
  } while (0)

-}

