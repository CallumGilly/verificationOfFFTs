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
open import Matrix.SubShape

private variable
  s q p q₁ q₂ : Shape
  n : ℕ

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


infixl 2 _>>>_
data Inp : Ty → Ty → Set where
  dft  : NonZero n → Inp (ar (ι 2 ⊗ ι n) R) (ar (ι 2 ⊗ ι n) R)
  twid : ⦃ NonZeroₛ (s ⊗ p) ⦄ → Inp (ar (ι 2 ⊗ (s ⊗ p)) R) (ar (ι 2 ⊗ (s ⊗ p)) R) 
  
  part : Inp (ar s τ) (ar q τ) → s ⊂ p → Inp (ar p τ) (ar p τ)  

  _>>>_ : Inp τ δ → Inp δ σ → Inp τ σ

  copy : Reshape s p → Inp (ar s τ) (ar p τ)

private variable
  BLOCKS LANES : ℕ

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

`ffti : NonZeroₛ s → Inp (ar (ι 2 ⊗ s) R) (ar (ι 2 ⊗ s) R)
`ffti (ι nz) = dft nz
`ffti (_⊗_ {p = p} nzs nzp) =
  part (`ffti nzs) (bothᵣ idh (left idh))
  >>> twid ⦃ nzs ⊗ nzp ⦄
  >>> part (`ffti nzp) (bothᵣ idh (right idh))
  >>> copy (eq ⊕ (♯ ∙ reindex (*-comm (size p) _) ∙ ♭ ∙ swap)) 

`transpose-test₁ : Inp (ar s R) (ar (s ᵗ) R)
`transpose-test₁ {s} = copy (recursive-transposeᵣ)

module Interp (real : Real) (cplx : Cplx) where
  open Cplx cplx renaming (_+_ to _+𝕔_; _*_ to _*𝕔_)
  open Real.Real real using (_ᵣ; ℝ)
  
  open import Matrix.Equality
  open import Matrix.Reshape
  open import FFT cplx using (twiddles; offset-prod; FFT′; FFT′′)
  open import Proof cplx

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
  sel-to-str ptr sel ixs = to-sel (ix-up sel ixs) ptr


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
  create-tmp-mem {s} ty sel op = do
    var ← fresh-var
    let declaration = printf "%s (*%s)%s = %s;" ty var (shape-helper s) (op s)
    return $ var , declaration

  create-hole-copy : (type : String) → String → Sel s p → State ℕ (String × String)
  create-hole-copy {s} ty ptr sel = do
    var , var-declaration ← create-tmp-mem ty sel (malloc-op ty)
    i ← generateIx s
    let copy-values = loop-nest s i $ printf "%s = %s;" (to-sel i var) (sel-to-str ptr sel i)
    return $ var , var-declaration ++ copy-values

  copy-into-sel : (fromPtr : String) → (toPtr : String) → Sel s p → State ℕ String
  copy-into-sel {s} fromPtr toPtr sel = do
    i ← generateIx s
    return $ loop-nest s i $ printf "%s = %s;" (sel-to-str toPtr sel i) (to-sel i fromPtr)

  use-dft-macro : ℕ → String → String → String
  use-dft-macro n xs ys = printf "SPLIT_DFT(%u, ((real (*)[%u])%s), ((real (*)[%u])%s));" n n xs n ys

  minus-omega : Component → (n : ℕ) → (j : String) → String
  minus-omega = printf "minus_omega_%s(%u, %s)" ∘ component-sym 

  to-vali : Inp τ σ → AR τ → State ℕ (String × AR σ)
  to-vali (dft {n} nz-n) (arr ptr sel) = do 
    j ← generateIx (ι n)
    inp-var , create-inp-mem  ← create-hole-copy real-type ptr sel
    out-var , declare-out-mem ← create-tmp-mem real-type sel (calloc-op real-type)
    let use-dft = use-dft-macro n inp-var out-var
    copy-out-to-ptr ← copy-into-sel out-var ptr sel
    return $ (create-inp-mem ++ declare-out-mem ++ use-dft ++ copy-out-to-ptr) , arr ptr sel
  to-vali (twid {s} {p}) (arr ptr sel) = do
    i ← generateIx (s ⊗ p)
    ----- I Really wish I had fin types here....
    let memSel_r = sel-to-str ptr sel ((component-ix REAL) ⊗ i)
    let memSel_i = sel-to-str ptr sel ((component-ix IMAG) ⊗ i)
    
    tmp-var ← fresh-var
    let init-tmp-var = printf "%s %s;\n" real-type tmp-var

    let ops =  (printf "%s = %s;\n" tmp-var memSel_r)
            ++ (printf 
                  "%s = (%s * %s) - (%s * %s);\n" 
                  memSel_r 
                  memSel_r 
                  (minus-omega REAL (size s * size p) (offset-prod i))
                  memSel_i
                  (minus-omega IMAG (size s * size p) (offset-prod i))
               )
            ++ (printf 
                  "%s = (%s * %s) + (%s * %s);\n" 
                  memSel_i 
                  tmp-var
                  (minus-omega IMAG (size s * size p) (offset-prod i))
                  memSel_i
                  (minus-omega REAL (size s * size p) (offset-prod i))
               )
    
    return $ (init-tmp-var ++ loop-nest (s ⊗ p) i ops , arr ptr sel)

  to-vali (part {s} {p = p} e s⊆p) (arr {s = t} ptr se) = 
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


  gen-fft : (s : Shape) → ⦃ _ : NonZeroₛ s ⦄ → String × String
  gen-fft s with show′ (num (arr R)) (arr "inp" idh) (fft s) "fft"
  ... | body , header = (preamble ++ header) , (preamble ++ body)

  gen-transpose-test : (s : Shape) → String × String
  gen-transpose-test s with show′ (num (arr R)) (arr "inp" idh) (`transpose-test₁ {s}) "transposeTest"
  ... | body , header = (preamble ++ header) , (preamble ++ body)


open Tests using (gen-fft; gen-transpose-test) public
