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
  dft  :  NonZero n → Inp (ar (ι n) C) (ar (ι n) C)
  twid : Inp (ar s C) (ar s C) 
  
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
  >>> twid
  >>> part-row (`ffti nzp) eq 
  >>> copy (♯ ∙ reindex (*-comm (size p) _) ∙ ♭ ∙ swap) -- TODO: check whether this is correct

module Interp (real : Real) (cplx : Cplx) where
  open Cplx cplx renaming (_+_ to _+𝕔_; _*_ to _*𝕔_)
  open Real.Real real using (_ᵣ)
  
  open import Matrix.Equality
  open import Matrix.Reshape
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

  -- Make aboev string to string

  ~-Num : τ ~ σ → Num τ → Num σ
  ~-Num sca C = C
  ~-Num (arr _ prf) (arr num-τ) = arr (~-Num prf num-τ)

  ~-Fut : τ ~ σ → Fut τ → Fut σ
  ~-Fut sca fut = fut
  ~-Fut (arr _ prf) (num (arr num-τ)) = num (arr (~-Num prf num-τ))

  {-
  inpFut : Inp Val τ σ → Fut τ → Fut σ
  inpFut (copy prf x₁) fut-τ = ~-Fut prf fut-τ
  inpFut (view x inp x₁) fut-τ = ?
  inpFut (mapi inp) fut-τ = ?
  inpFut (zipw x x₁) fut-τ = ?
  inpFut (inp >>> inp₁) fut-τ = ?
  -}


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
  to-sel i a = printf "(*%s)%s" a $ ix-join (ix-map (printf "[%s]") i) ""
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

  to-str : Fut τ → Val τ → (res : String) → Op → State ℕ (String × String)
  to-val : E Val τ → {- (res op : String)  → -} State ℕ (String × Val τ)

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

  loop-nest-helper : (s : Shape) → Ix s → (String → String)
  loop-nest-helper (ι n    ) (ι i    ) = for-template i n
  loop-nest-helper (sₗ ⊗ sᵣ) (iₗ ⊗ iᵣ) = loop-nest-helper sₗ iₗ ∘ loop-nest-helper sᵣ iᵣ

  loop-nest : Fut τ → (res : String) → Op → (Ix s → State ℕ (String × Val τ)) → State ℕ (String × String)
  loop-nest {s = s} fut res op body =
    do 
      i ← generateIx s
      body-pre , body-val ← body i
      body-ass ← to-str fut body-val (sel-res op i) +=
      return $ "" , loop-nest-helper s i (body-pre ++ (proj₂ body-ass))
    where
      sel-res : Op → Ix s → String
      sel-res += _ = res
      sel-res ≔  i = to-sel i res

  shape-helper : Shape → String
  shape-helper (ι n)   = printf "[%u]" n
  shape-helper (s ⊗ p) = shape-helper s ++ shape-helper p

  shape-to-arg : Shape → String → String
  shape-to-arg (ι n)   res = printf "(*%s)[%u]" res n
  shape-to-arg (s ⊗ p) res = shape-to-arg s res ++ shape-helper p


  --to-val′ : Inp Val τ σ → (adr : String) → {- (res op : String)  → -} State ℕ (String × Val τ)


  Var : (τ : Ty) → Num τ → Set
  Var C C = String
  Var (ix s ⇒ τ) (arr n) = Ix s → Var τ n

  rshp-ix : Reshape s p → Ix p → Ix s
  rshp-ix eq x₁ = x₁
  rshp-ix (x ∙ x₂) x₁ = (rshp-ix x₂ (rshp-ix x x₁))
  rshp-ix (x ⊕ x₂) (x₁ ⊗ x₃) = (rshp-ix x x₁) ⊗ (rshp-ix x₂ x₃)
  rshp-ix (split {m}) (ι x ⊗ ι x₁) = ι (printf "((%s * %u) + %s)" x m x₁)
  rshp-ix (flat {m} {n}) (ι x) = ι (printf "%s / %u" x n) ⊗ ι (printf "%s %% %u" x n) -- TODO: Check this
    --ι (printf "TODO: Flatten %s" ?) ⊗ ι ("TODO2: Flatten")
    --Goal Type : Ix (ι m ⊗ ι n)
  rshp-ix Reshape.swap (x₁ ⊗ x₂) = x₂ ⊗ x₁

  data Sel : (s : Shape) → (p : Shape) → Set where
    sel-id :        Sel s s
    left   : Ix p → Sel q s → Sel q (s ⊗ p)
    right  : Ix s → Sel q p → Sel q (s ⊗ p)

  sub-right : Sel (s ⊗ p) q → Ix s → Sel p q
  sub-right sel-id i = right i sel-id
  sub-right (left j h) i = left j (sub-right h i)
  sub-right (right j h) i = right j (sub-right h i)

  sub-left : Sel (s ⊗ p) q → Ix p → Sel s q
  sub-left sel-id i = left i sel-id
  sub-left (left j h) i = left j (sub-left h i)
  sub-left (right j h) i = right j (sub-left h i)

  data AR : Ty → Set where
    cst : String → AR C
    arr : String → Sel p s → AR (ar p C)


  sel-to-str : String → Sel s p → Ix s → String
  sel-to-str ptr sel-id ixs = to-sel ixs ptr
  sel-to-str ptr (left ixp sel) ixs = to-sel ixp (sel-to-str ptr sel ixs)
  sel-to-str ptr (right ixs sel) ixp = sel-to-str (to-sel ixs ptr) sel ixp

  do-dft : (n : ℕ) → String → String → Sel (ι n) s → State ℕ (String)
  do-dft n inp-ptr out-ptr out-sel = do
    mem-out ← fresh-var
    let setup-out = printf "complex* %s = calloc(0, (sizeof %s));" mem-out inp-ptr

    let do-dft = printf "dft(*%s, *%s);" inp-ptr mem-out

    j ← generateIx (ι n)
    let cp-out = loop-nest-helper (ι n) j $ printf "%s = %s;" (sel-to-str out-ptr out-sel j) (to-sel j mem-out)

    return $ setup-out ++ do-dft ++ cp-out

  to-vali : Inp τ σ → AR τ → State ℕ (String × AR σ)
  to-vali (dft {n} nz-n) (arr ptr sel-id) = do
    op ← do-dft n ptr ptr sel-id
    return $ op , arr ptr sel-id
  to-vali (dft {n} nz-n) (arr ptr (left x se)) = do
    mem-inp ← fresh-var
    let setup-inp = printf "complexType* %s = calloc(0, (%u * sizeof(complexType)));" mem-inp n

    i ← generateIx (ι n)
    let cp-inp = loop-nest-helper (ι n) i $ printf "%s = %s;" (to-sel i mem-inp) (sel-to-str ptr (left x se) i)

    op ← do-dft n mem-inp ptr (right x se)
    return $ (setup-inp ++ cp-inp ++ op) , arr ptr se
  to-vali (dft {n} nz-n) (arr ptr (right x se)) = do
    op ← do-dft n (to-sel x ptr) ptr (left x se)
    return $ op , arr ptr se
  to-vali (twid {s}) (arr {s = p} ptr sel) =
    do
      i ← generateIx s
      let memSel = sel-to-str ptr sel i
      return $ (loop-nest-helper s i (printf "%s *= minus_omega(%u , %s);\n" memSel (size s) (offset i))) , arr ptr sel
  to-vali (part-col {p = p} e eq) (arr ptr se) = do
    i ← generateIx p
    expr , _ ← (to-vali e (arr ptr (sub-left  se i)))
    return $ (loop-nest-helper p i expr) , arr ptr se
  to-vali (part-row {s = s} e eq) (arr ptr se) = do
    i ← generateIx s
    expr , _ ← (to-vali e (arr ptr (sub-right se i)))
    return $ (loop-nest-helper s i expr) , arr ptr se
  to-vali {τ} (inp₁ >>> inp₂) arτ = do
    e₁ , ARδ ← to-vali inp₁ arτ
    e₂ , ARσ ← to-vali inp₂ ARδ
    return $ (e₁ ++ e₂) , ARσ
  to-vali (copy {s = s} {p = p} rshp) (arr ptr se) = do
    working-mem ← fresh-var
    let setup-tmp     = printf "complexType* %s = malloc(sizeof %s);" working-mem ptr
    
    i ← generateIx s
    let copy-to-tmp   = loop-nest-helper s i $ printf "%s = %s;" (sel-to-str working-mem se i) (sel-to-str ptr se i)

    j ← generateIx p
    let copy-from-tmp = loop-nest-helper p j $ printf "%s = %s;\n// TODO: This will breakdown when se is not empty" 
                          (to-sel j ptr) 
                          (sel-to-str working-mem se (rshp-ix rshp j))

    let free-tmp      = ""
    return $ (setup-tmp ++ copy-to-tmp ++ copy-from-tmp ++ free-tmp) , arr working-mem sel-id
  
  --to-vali : (inp : Inp τ σ) → {τ-n : Num τ} →{- Fut τ → Fut σ → -} (mem : (String)) → State ℕ (String × (String))
  --to-vali (dft {n} nz)     mem = return $ "\n//TODO: DFT\n" , mem
  --to-vali (twid {s})  mem = do 
  --  i ← generateIx s
  --  let memSel = (to-sel i mem)
  --  let loop = loop-nest-helper s i 
  --  return $ loop (printf "%s *= minus_omega(%u , %s); //TODO: CHECK THIS IS CORRECT TWIDDLE USE\n" memSel (size s) (offset i)) 
  --          , mem 
  --to-vali (part-col {s} inp eq) {arr τ-n} mem = return $ "\n//TODO: PART-COL\n" , mem
  --to-vali (part-row {s} inp eq) {arr τ-n} mem = do
  --  i ← generateIx s
  --  inner , _ ← to-vali inp {arr τ-n} (to-sel i mem)
  --  return $ loop-nest-helper s i inner , mem
  --to-vali {τ} {σ} (_>>>_ inp₁ inp₂) {τ-n} mem =
  --  do
  --    inp₁-pre , inp₁-var ← to-vali inp₁ {τ-n} mem
  --    inp₂-pre , inp₂-var ← to-vali inp₂ {toNum inp₁ τ-n} inp₁-var
  --    return $ inp₁-pre ++ inp₂-pre , inp₂-var
  --to-vali (copy {s} {p} rshp) {τ-n} mem = do
  --  tmp_var ← fresh-var
  --  orig-i ← generateIx s
  --  let orig-i′ = (rshp-ix (rev rshp) orig-i)
  --  rshp-i ← generateIx p
  --  let rshp-i′ = (rshp-ix (rshp) rshp-i)
  --  return $  (  (printf "%s = malloc(sizeof %s);\n" tmp_var mem)
  --            ++ (loop-nest-helper s orig-i (printf "%s = %s;" (to-sel orig-i tmp_var) (to-sel orig-i′ mem    )))
  --            ++ (loop-nest-helper p rshp-i (printf "%s = %s;" (to-sel rshp-i mem    ) (to-sel rshp-i tmp_var)))
  --            ++ (printf "free(%s);" tmp_var)
  --            ) , mem


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

  to-str (num C) v res op = return $ "" , printf "%s %s %s;" res (op-str op) v
  to-str (num (arr x)) v res op = loop-nest (num x) res op v
  -- We currently only want to deal with functions which accept and array, and 
  -- return an array, for now therefore we can throw an error instead of producing
  -- code for all other inputs
  to-str (fun {τ} {σ} inp out) val res op =
    do
      n ← get
      modify suc
      let arg-name = (fresh n)
      arg ← num-var inp arg-name
      str-pre , β-val ← val arg
      str-val ← to-str {σ} out β-val res op
      return $ 
          (printf "void %s(%s, %s);\n" 
            res 
            (ty-to-arg (num inp) arg-name)
            (ty-to-arg out res))
        , 
          printf "void %s(%s, %s) {\n%s\n}" 
            res 
            (ty-to-arg (num inp) arg-name)
            (ty-to-arg out res)
            (str-pre ++ proj₂ str-val)

  show′ : (AR τ) → (Inp τ σ) → String
  show′ ARτ e = runState (
      do
        val , mem ← to-vali e ARτ
        return $ val
    ) 0 .proj₂

  show : Fut τ → (∀ {V} → E V τ) → String → String × String
  show p e res = runState ( 
      do 
          (deps , val) ← to-val e
          result ← to-str p val res ≔
          return $ deps ++ (proj₁ result) , deps ++ proj₂ result
    ) 0 .proj₂

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

  --dft : (n : ℕ) → ⦃ NonZero n ⦄ → E V _
  --dft n = `dft {n}

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

  show-test : String → (∀ {V} → E V τ) → True (isFut τ) → String × String
  show-test {τ = τ} name e t with isFut τ
  ... | yes p = show p e name

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
           ++ "#include \"../src/minus-omega.h\"\n"

  --gen-fft : (s : Shape) → ⦃ _ : NonZeroₛ s ⦄ → String × String
  --gen-fft s = preamble , preamble ++ (show′ (fft s) "fft")
  --with show-test′ "fft" (fft s) 
  --... | body = preamble , preamble ++ body
  -- _ : gen-fft (ι 3 ⊗ ι 3) ⦃ ι (record { nonZero = tt }) ⊗ ι (record { nonZero = tt }) ⦄ ≡ ?
  -- _ = ?

  gen-fft : (s : Shape) → ⦃ _ : NonZeroₛ s ⦄ → String × String
  gen-fft s with show′ (arr "inp" (sel-id)) (fft s)
  ... | body = preamble , (preamble ++ body)


  --preamble , preamble ++ (show′ ? (fft s) "fft")
  --with show-test′ "fft" (fft s) 
  --... | body = preamble , preamble ++ body

  --_ : gen-fft (ι 3 ⊗ ι 3) ⦃ ι (record { nonZero = tt }) ⊗ ι (record { nonZero = tt }) ⦄ ≡ ?
  --_ = ?

  --gen-dft : (n : ℕ) → ⦃ _ : NonZero n ⦄ → String × String
  --gen-dft n with show-test "dft" (dft n) _ 
  --... | head , body = preamble ++ head , preamble ++ body

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

