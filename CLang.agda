--{-# OPTIONS --backtracking-instance-search #-}
{-# OPTIONS --guardedness #-}

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties using (*-comm)
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
  τ σ δ ψ : Ty

data Num : Ty → Set where
  C   : Num C
  arr : Num τ → Num (ix s ⇒ τ)

data Fut : Ty → Set where
  num : Num τ → Fut τ
  fun : Num τ → Fut σ → Fut (τ ⇒ σ)

data T : Ty → Ty → Set where
  idₜ : T (ar s τ) (ar s τ)
  _⊡_ : T (ar s σ) (ar q δ) → T (ar p τ) (ar s σ) → T (ar p τ) (ar q δ)
  swapₜ : T (ar (s ⊗ p) τ) (ar (p ⊗ s) τ)
  nestₜ   : T (ar (s ⊗ p) τ) (ar s (ar p τ))
  unnestₜ : T (ar s (ar p τ)) (ar (s ⊗ p) τ)

data E (V : Ty → Set) : Ty → Set

data _~_ : Ty → Ty → Set where
  sca : C ~ C
  arr : Reshape s p → τ ~ σ → ar s τ ~ ar p σ

-- Inp V τ σ ~ τ ⇒ σ | 
--   void(τ a, σ *r) {
--      reuse(a, e₁)
--      ...
--      r = a
--   }
{- 
infixl 2 _>>>_
data Inp (V : Ty → Set) : Ty → Ty → Set where
  copy : τ ~ σ → E V (τ ⇒ σ) → Inp V τ σ
  view : T τ δ → Inp V δ ψ → T ψ σ → Inp V τ σ 
  mapi : Inp V τ σ → Inp V (ar s τ) (ar s σ)
  -- TODO: Generalise
  zipw : E V (ar s C)
       → E V (C ⇒ C ⇒ C)
       → Inp V (ar s C) (ar s C)
  _>>>_ : Inp V τ δ → Inp V δ σ → Inp V τ σ
-}

data Copy : Shape → Shape → Set where
  eq : Copy s s

infixl 2 _>>>_
data Inp : Ty → Ty → Set where
  dft  : NonZero n → Inp (ar (ι n) C) (ar (ι n) C)
  twid : ⦃ NonZeroₛ (s ⊗ p) ⦄ → Inp (ar (s ⊗ p) C) (ar (s ⊗ p) C) 
  
  part-col : Inp (ar s τ) (ar q τ) → Copy s q → Inp (ar (s ⊗ p) τ) (ar (q ⊗ p) τ)
  part-row : Inp (ar p τ) (ar q τ) → Copy p q → Inp (ar (s ⊗ p) τ) (ar (s ⊗ q) τ)
  
  _>>>_ : Inp τ δ → Inp δ σ → Inp τ σ

  copy : Reshape s p → Inp (ar s τ) (ar p τ)


infixl 3 _`$_
--infixl 2 _`>>=_
data E V where
  `     : (V τ) → E V τ
  `lam  : (V τ → E V σ) → E V (τ ⇒ σ)
  _`$_  : E V (τ ⇒ σ) →  E V τ → E V σ
  _`⊗_  : E V (ix s) → E V (ix p) → E V (ix (s ⊗ p))
  `sum  : E V (ar (ι n) C) → E V C
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

`dft : ⦃ NonZero n ⦄ → E V (ar (ι n) C ⇒ ar (ι n) C)
`dft {n = n} = `λ a ⇒ `λ j ⇒ `sum (`λ k ⇒ (` a `$ ` k) `* `ω n (` k `⊗ ` j))

`twid : ⦃ NonZeroₛ (s ⊗ p) ⦄ → E V (ar (s ⊗ p) C)
`twid {s = s}{p} ⦃ nz ⦄ = `λ i ⇒ `ω (size (s ⊗ p)) ⦃ nz-# nz ⦄ (` i)

`ffti : NonZeroₛ s → Inp (ar s C) (ar s C)
`ffti (ι nz)      = dft nz
`ffti (_⊗_ {p = p} nzs nzp) = 
  part-col (`ffti nzs) eq
  >>> twid ⦃ nzs ⊗ nzp ⦄
  >>> part-row (`ffti nzp) eq 
  >>> copy (♯ ∙ reindex (*-comm (size p) _) ∙ ♭ ∙ swap) -- TODO: check whether this is correct

module Interp (real : Real) (cplx : Cplx) where
  open Cplx cplx renaming (_+_ to _+𝕔_; _*_ to _*𝕔_)
  open Real.Real real using (_ᵣ)
  
  open import Matrix.Equality
  open import Matrix.Reshape
  open import FFT cplx using (twiddles; offset-prod; FFT′; FFT′′)
  open import Proof cplx

  Sem : Ty → Set
  Sem C = ℂ
  Sem (ix x) = Position x
  Sem (τ ⇒ σ) = Sem τ → Sem σ

  fst : Position (s ⊗ p) → Position s
  fst (i ⊗ j) = i

  snd : Position (s ⊗ p) → Position p
  snd (i ⊗ j) = j

  interp-T : T (ar s τ) (ar p σ) → (Sem (ar s τ)) → (Position p → Sem σ)
  interp-T idₜ         ⟦e⟧         = ⟦e⟧
  interp-T (t₁ T.⊡ t₂) ⟦e⟧         = interp-T t₁ $ interp-T t₂ ⟦e⟧ 
  interp-T swapₜ       ⟦e⟧ (l ⊗ r) = ⟦e⟧ (r ⊗ l)
  interp-T nestₜ       ⟦e⟧ l       = λ r → ⟦e⟧ (l ⊗ r)
  interp-T unnestₜ     ⟦e⟧ (l ⊗ r) = ⟦e⟧ l r

  interp : E Sem τ → Sem τ
  interp (` x) = x
  interp (`lam f) x = interp (f x)
  interp (e `$ e₁) = interp e (interp e₁)
  interp (e `⊗ e₁) = interp e ⊗ interp e₁
  interp (`sum e) = sum (interp e)
  interp (`ω n e) = -ω n (offset-prod (interp e))
  interp (e `* e₁) = interp e *𝕔 interp e₁

  interp-inp : Inp τ σ → Sem τ → Sem σ
  interp-inp (dft nz) ar = λ p → interp (`dft ⦃ nz ⦄ `$ (` ar) `$ (` p))
  interp-inp (twid {s} {p} ⦃ nz-s⊗p ⦄ ) ar = zipWith _*𝕔_ ar (twiddles ⦃ nz-s⊗p ⦄)
  interp-inp (part-col inp eq) = reshape swap ∘ unnest ∘ map (interp-inp inp) ∘ nest ∘ reshape swap 
  interp-inp (part-row inp eq) =                unnest ∘ map (interp-inp inp) ∘ nest
  interp-inp (inp₁ >>> inp₂) = interp-inp inp₂ ∘ interp-inp inp₁
  interp-inp (copy rshp) = reshape rshp

  --inpfft-ok :  ⦃ nz-s : NonZeroₛ s ⦄ → ∀ a → FFT′′ {s} a ≅ interp-inp (`ffti nz-s) a
  --inpfft-ok {ι N} ⦃ ι nz-N ⦄ a i = refl
  --inpfft-ok {r₁ ⊗ r₂} ⦃ nz-r₁ ⊗ nz-r₂ ⦄ a (i ⊗ j) =
  --  begin
  --    _ ≡⟨ ? ⟩
  --    --_ ≡⟨ FFT′′-cong ⦃ ? ⦄ (λ k → cong₂ _*𝕔_ (inpfft-ok ⦃ ? ⦄ _ j) refl) i ⟩
  --    _
  --  ∎ where open ≡-Reasoning

  -- interp (`view x e) = interp-T x $ interp e
  -- interp (`transform x e) = interp-T x $ interp e
  -- interp (a `>>= a₁) = interp a₁ $ interp a

  -- I hate stupid instances!
  --efft-ok :  ⦃ _ : NonZeroₛ s ⦄ → ∀ a → FFT′ {s} a ≅ interp `fft a
  --efft-ok ⦃ ι nz    ⦄ a i       = refl
  --efft-ok ⦃ ns ⊗ np ⦄ a (i ⊗ j) =
  --  begin
  --    _ ≡⟨ FFT′-cong ⦃ np ⦄ (λ k → cong₂ _*𝕔_ (efft-ok ⦃ ns ⦄ _ j) refl) i ⟩
  --    _ ≡⟨ efft-ok ⦃ np ⦄ _ i ⟩
  --    _
  --  ∎ where open ≡-Reasoning


module ShowC where
  open import Data.Nat
  open import Data.String hiding (show)
  open import Data.Product
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

  offset-prod : Ix s → String
  offset-prod (ι x) = x
  offset-prod {s ⊗ p} (i ⊗ j) = printf "(%s * %s)" (offset-prod i) (offset-prod j)

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

  --to-str : Fut τ → Val τ → (res : String) → Op → State ℕ (String × String)
  --to-val : E Val τ → {- (res op : String)  → -} State ℕ (String × Val τ)

  for-template : String → ℕ → String → String
  for-template i n expr = printf "for (size_t %s = 0; %s < %u; %s++) {\n%s\n}" i i n i expr

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

  shape-to-arg : Shape → String → String
  shape-to-arg (ι n)   res = printf "(*%s)[%u]" res n
  shape-to-arg (s ⊗ p) res = shape-to-arg s res ++ shape-helper p

  Var : (τ : Ty) → Num τ → Set
  Var C C = String
  Var (ix s ⇒ τ) (arr n) = Ix s → Var τ n

  rshp-ix : Reshape s p → Ix p → Ix s
  rshp-ix eq x₁ = x₁
  rshp-ix (x ∙ x₂) x₁ = (rshp-ix x₂ (rshp-ix x x₁))
  rshp-ix (x ⊕ x₂) (x₁ ⊗ x₃) = (rshp-ix x x₁) ⊗ (rshp-ix x₂ x₃)
  rshp-ix (split {m} {n}) (ι x ⊗ ι x₁) = ι (printf "((%s * %u) + %s)" x n x₁)
  rshp-ix (flat {m} {n}) (ι x) = ι (printf "(%s / %u)" x n) ⊗ ι (printf "(%s %% %u)" x n) -- TODO: Check this
  rshp-ix Reshape.swap (x₁ ⊗ x₂) = x₂ ⊗ x₁
  
  data Sel : Shape → Shape → Set where
    idh   : Sel s s
    view  : Sel s p → Reshape q s → Sel q p
    chain : Sel s p → Sel p q → Sel s q
    left  : Ix p → Sel q s → Sel q (s ⊗ p)
    right : Ix s → Sel q p → Sel q (s ⊗ p)

  sub-right : Sel (s ⊗ p) q → Ix s → Sel p q
  sub-right idh          i = right i idh
  sub-right (view  se r) i = chain  (right i idh) (view se r)
  sub-right (chain a  b) i = chain   (sub-right a i) b
  sub-right (left  j  h) i = left  j (sub-right h i)
  sub-right (right j  h) i = right j (sub-right h i)

  sub-left : Sel (s ⊗ p) q → Ix p → Sel s q
  sub-left idh          i = left  i idh
  sub-left (view  se r) i = chain   (left i idh) (view se r)
  sub-left (chain a  b) i = chain   (sub-left a i) b
  sub-left (left  j  h) i = left  j (sub-left h i)
  sub-left (right j  h) i = right j (sub-left h i)

  data AR : Ty → Set where
    cst : String → AR C
    arr : String → Sel p s → AR (ar p C)

  reix : Ix s → Reshape s p → Ix p
  reix ixs rshp = rshp-ix (rev rshp) ixs 

  ix-up : Sel s p → Ix s → Ix p
  ix-up idh i = i
  ix-up (view se x)    i = ix-up se (reix i x)
  ix-up (chain se se₁) i = ix-up se₁ (ix-up se i)
  ix-up (left x se)    i = ix-up se i ⊗ x
  ix-up (right x se)   i = x ⊗ ix-up se i

  rshp-sel-to-str : Reshape s p → (ptr : String) → Sel s q → Ix p → String
  rshp-sel-to-str rshp ptr idh            ixp = to-sel ixp ptr
  rshp-sel-to-str rshp ptr (view se x)    ixp = "\n//TODO View\n"
  rshp-sel-to-str rshp ptr (chain se se₁) ixp = "\n//TODO Chain\n"
  rshp-sel-to-str rshp ptr (left ixq se)    ixp = to-sel′ ixq (rshp-sel-to-str rshp ptr se ixp) 
  rshp-sel-to-str rshp ptr (right ixs se)   ixp = rshp-sel-to-str rshp (to-sel′ ixs ptr) se ixp

  sel-to-str : String → Sel s p → Ix s → String
  sel-to-str ptr sel ixs = to-sel (ix-up sel ixs) ptr

  malloc-op : Shape → String
  malloc-op = printf "malloc(%u * sizeof(complex float))" ∘ size

  calloc-op : Shape → String
  calloc-op = printf "calloc(%u, sizeof(complex float))" ∘ size

  create-tmp-mem : Sel s p → (Shape → String) → State ℕ (String × String)
  create-tmp-mem {s} sel op = do
    var ← fresh-var
    let declaration = printf "complex float (*%s)%s = %s;" var (shape-helper s) (op s)
    return $ var , declaration

  create-hole-copy : String → Sel s p → State ℕ (String × String)
  create-hole-copy {s} ptr sel = do
    var , var-declaration ← create-tmp-mem sel malloc-op
    i ← generateIx s
    let copy-values = loop-nest s i $ printf "%s = %s;" (to-sel i var) (sel-to-str ptr sel i)
    return $ var , var-declaration ++ copy-values

  copy-into-sel : (fromPtr : String) → (toPtr : String) → Sel s p → State ℕ String
  copy-into-sel {s} fromPtr toPtr sel = do
    i ← generateIx s
    return $ loop-nest s i $ printf "%s = %s;" (sel-to-str toPtr sel i) (to-sel i fromPtr)

  use-dft-macro : ℕ → String → String → String
  use-dft-macro = printf "DFT(%u, (*%s), (*%s));"

  to-vali : Inp τ σ → AR τ → State ℕ (String × AR σ)
  to-vali (dft {n} nz-n) (arr ptr sel) = do
    j ← generateIx (ι n)
    inp-var , create-inp-mem  ← create-hole-copy ptr sel
    out-var , declare-out-mem ← create-tmp-mem sel calloc-op
    let use-dft = use-dft-macro n inp-var out-var
    copy-out-to-ptr ← copy-into-sel out-var ptr sel
    return $ (create-inp-mem ++ declare-out-mem ++ use-dft ++ copy-out-to-ptr) , arr ptr sel
  to-vali (twid {s} {p}) (arr ptr sel) =
    do
      i ← generateIx (s ⊗ p)
      let memSel = sel-to-str ptr sel i
      return $ (loop-nest (s ⊗ p) i (printf "%s = %s * minus_omega(%u , %s);\n" memSel memSel (size s * size p) (offset-prod i))) , arr ptr sel
  to-vali (part-col {p = p} e eq) (arr ptr se) = do
    i ← generateIx p
    expr , _ ← (to-vali e (arr ptr (sub-left  se i)))
    return $ (loop-nest p i expr) , arr ptr se
  to-vali (part-row {s = s} e eq) (arr ptr se) = do
    i ← generateIx s
    expr , _ ← (to-vali e (arr ptr (sub-right se i)))
    return $ (loop-nest s i expr) , arr ptr se
  to-vali {τ} (inp₁ >>> inp₂) arτ = do
    e₁ , ARδ ← to-vali inp₁ arτ
    e₂ , ARσ ← to-vali inp₂ ARδ
    return $ (e₁ ++ e₂) , ARσ
  to-vali (copy {s = s} {p = p} rshp) (arr ptr se) = do
    working-mem , copy-out ← create-hole-copy ptr se

    i ← generateIx p
    let copy-in = loop-nest p i $ printf "%s = %s;" (rshp-sel-to-str rshp ptr se i) (to-sel (rshp-ix rshp i) working-mem)

    return $ copy-out ++ copy-in , arr ptr idh

















  {-
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
  to-val (`sum e) = do
    fresh-res ← fresh-var 
    def , array-summed ← to-val e
    s ← to-str (num (arr C)) array-summed fresh-res +=
    return (def ++ (printf "complex float %s = 0;\n" fresh-res) ++ (proj₂ s) , fresh-res)
  to-val (`ω n e)  = do
    (d , k) ← to-val e
    return ( d , omega n k )
  to-val (l `* r) = do
    ld , lx ← to-val l
    rd , rx ← to-val r
    return (ld ++ rd , printf "(%s * %s)" lx rx)
  -}
  --to-val (`view x a)      = do
  --  ?
  --to-val (`transform x a) = ?
  ---- For variables, and prior binding, we know where to bind to, otherwise however...
  --to-val (e₁ `>>= e₂) = ?
  --  do
  --    let assingmentLocation = ""
  --    e₁-pre , e₁-val ← to-val e₁
  --    e₂-pre , e₂-val ← to-val (e₂ `$ ` "ASSINGMENTLOC")
  --    return $ ? , ?


  num-type : Num τ → String
  num-type C = "complex float "
  num-type {ix s ⇒ τ} (arr x) = num-type {τ} x ++ (shape-helper s)
  
  final-type : Fut τ → String
  final-type (num x) = num-type x
  final-type (fun x fut) = final-type fut
  
  parameter-list-app : Fut τ → String → String
  parameter-list-app (num x)    pre = pre
  parameter-list-app (fun x next) pre = parameter-list-app next (printf "%s , %s" pre (num-type x))

  ty-to-arg : Fut τ → String → String
  ty-to-arg {C} (num x) res = printf "complex float (*%s)" res
  ty-to-arg {ix s ⇒ C} (num (arr C)) res = "complex float " ++ shape-to-arg s res
  ty-to-arg {ix s ⇒ (ix p ⇒ τ)} (num (arr (arr x))) res = ty-to-arg {ix p ⇒ τ} (num (arr x)) res ++ shape-helper s
  -- The below case is the one I have been struggling to work out how to deal with...
  ty-to-arg {τ ⇒ σ} (fun x fut) res = printf "%s (*%s) (%s)" (final-type fut) res (parameter-list-app fut (num-type x))

  --to-str (num C) v res op = return $ "" , printf "%s %s %s;" res (op-str op) v
  --to-str (num (arr x)) v res op = loop-nest (num x) res op v
  ---- We currently only want to deal with functions which accept and array, and 
  ---- return an array, for now therefore we can throw an error instead of producing
  ---- code for all other inputs
  --to-str (fun {τ} {σ} inp out) val res op =
  --  do
  --    n ← get
  --    modify suc
  --    let arg-name = (fresh n)
  --    arg ← num-var inp arg-name
  --    str-pre , β-val ← val arg
  --    str-val ← to-str {σ} out β-val res op
  --    return $ 
  --        (printf "void %s(%s, %s);\n" 
  --          res 
  --          (ty-to-arg (num inp) arg-name)
  --          (ty-to-arg out res))
  --      , 
  --        printf "void %s(%s, %s) {\n%s\n}" 
  --          res 
  --          (ty-to-arg (num inp) arg-name)
  --          (ty-to-arg out res)
  --          (str-pre ++ proj₂ str-val)

  AR-name : AR τ → String
  AR-name (cst name  ) = name
  AR-name (arr name _) = name

  show′ : Fut τ → (AR τ) → (Inp τ σ) → String → String × String
  show′ fut ARτ e fName = runState (
      do
        let arg = ty-to-arg fut $ AR-name ARτ
        val , mem ← to-vali e ARτ
        return $ (printf "void %s(%s) { %s }" fName arg val) , (printf "void %s(%s);" fName arg)
    ) 0 .proj₂

  --show : Fut τ → (∀ {V} → E V τ) → String → String × String
  --show p e res = runState ( 
  --    do 
  --        (deps , val) ← to-val e
  --        result ← to-str p val res ≔
  --        return $ deps ++ (proj₁ result) , deps ++ proj₂ result
  --  ) 0 .proj₂

module Tests where
  open import Data.Empty
  open import Relation.Nullary
  open import Data.String hiding (show)
  open import Agda.Builtin.Unit using (tt)
  open import Data.Product

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

  fft : (s : Shape) → ⦃ _ : NonZeroₛ s ⦄ → Inp _ _
  fft s ⦃ nz ⦄ = `ffti nz

  Edft : (n : ℕ) → ⦃ NonZero n ⦄ → E V _
  Edft n = `dft {n}

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
  -- test₃ :  E V (ar sh C ⇒ ar _ C) 
  -- test₃ = `λ a ⇒ `swap (` a)

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

  --show-test : String → (∀ {V} → E V τ) → True (isFut τ) → String × String
  --show-test {τ = τ} name e t with isFut τ
  --... | yes p = show p e name

  --show-test′ : String → Inp τ σ → String
  --show-test′ {τ} name inp = show′ ? inp

  {-
  show-test′ : String → Inp τ σ → String
  show-test′ {τ} name inp with isNum τ 
  ... | no ¬a = "ERROR (Can probably elim with absurd)"
  ... | yes a = show′ a inp name
  -}
  --show-test′ : String → (∀ {V} → Inp V τ σ) → String × String
  --show-test′ {τ = τ} name e = let tm =  show′ e name in ?

  preamble : String
  preamble = "#include <complex.h>\n" 
           ++ "#include <stddef.h>\n"
           ++ "#include <stdlib.h>\n"
           ++ "#include \"../src/minus-omega.h\"\n"

  --gen-fft : (s : Shape) → ⦃ _ : NonZeroₛ s ⦄ → String × String
  --gen-fft s = preamble , preamble ++ (show′ (fft s) "fft")
  --with show-test′ "fft" (fft s) 
  --... | body = preamble , preamble ++ body
  -- _ : gen-fft (ι 3 ⊗ ι 3) ⦃ ι (record { nonZero = tt }) ⊗ ι (record { nonZero = tt }) ⦄ ≡ ?
  -- _ = ?

  gen-fft : (s : Shape) → ⦃ _ : NonZeroₛ s ⦄ → String × String
  gen-fft s with show′ (num (arr C)) (arr "inp" idh) (fft s) "fft"
  ... | body , header = (preamble ++ "#include \"../src/dft.h\"\n" ++ header) , (preamble ++ "#include \"../src/dft.h\"\n" ++ body)


  --preamble , preamble ++ (showgenerated′ ? (fft s) "fft")
  --with show-test′ "fft" (fft s) 
  --... | body = preamble , preamble ++ body

  --_ : gen-fft (ι 3 ⊗ ι 3) ⦃ ι (record { nonZero = tt }) ⊗ ι (record { nonZero = tt }) ⦄ ≡ ?
  --_ = ?

  -- gen-dft : (n : ℕ) → ⦃ _ : NonZero n ⦄ → String × String
  -- gen-dft n with show-test "dft" (Edft n) _ 
  -- ... | head , body = preamble ++ head , preamble ++ body

  --res : String × String
  --res = show-test "test" fft-mini _

open Tests using (gen-fft) public

module Print where
  open ShowC
  open Tests

  open import IO using (IO; run; Main; _>>_; _>>=_)
  open import IO.Finite using (putStrLn)
  open import Data.Unit.Polymorphic.Base using (⊤)
  open import Data.String hiding (show)
  open import Data.Product

  --main : Main
  --main = run $ putStrLn $  "#include <complex.h>\n" 
  --                      ++ "#include <stddef.h>\n"
  --                      ++ "#include \"../src/minus-omega.h\"\n"
  --                      ++ proj₂ res

