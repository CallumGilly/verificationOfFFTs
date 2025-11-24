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

--`ffti : ⦃ NonZeroₛ s ⦄ → Inp V (ar s C) (ar (s ᵗ) C)
--`ffti ⦃ ι nz    ⦄ = copy (arr eq sca) (`dft ⦃ nz ⦄)
--`ffti ⦃ ns ⊗ np ⦄ = view (nestₜ ⊡ swapₜ) (mapi (`ffti ⦃ ns ⦄)) (swapₜ ⊡ unnestₜ)
--                    >>> view swapₜ
--                             (zipw (`twid ⦃ np ⊗ nzᵗ ns ⦄) 
--                                   (`λ x ⇒ `λ y ⇒ ` x `* ` y))
--                             swapₜ
--                    >>> view nestₜ (mapi (`ffti ⦃ np ⦄)) (swapₜ ⊡ unnestₜ)


-- `fft : ⦃ NonZeroₛ s ⦄ → E V (ar s C ⇒ ar (s ᵗ) C)
-- `fft ⦃ ι nz ⦄ = `dft ⦃ nz ⦄
-- `fft ⦃ ns ⊗ np ⦄ = `λ a ⇒ 
--    ` a 
--      `>>= (`λ a ⇒ 
--      `view (swapₜ ⊡ unnestₜ) (`mapₐ `$ `fft ⦃ ns ⦄ `$ `view (nestₜ ⊡  swapₜ) (` a))
--    ) `>>= (`λ r1 ⇒
--      `view swapₜ (`λ i ⇒ (`view swapₜ (` r1) `$ ` i) `* (`twid ⦃ np ⊗ nzᵗ ns ⦄ `$ ` i))
--    ) `>>= (`λ rt ⇒ 
--      `view (swapₜ ⊡ unnestₜ) (`mapₐ `$ `fft ⦃ np ⦄ `$ (`view nestₜ (` rt)))
--    )

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

  {- 
  tmp₂ : Inp Val δ σ → Fut σ → Fut δ
  tmp₂ {C} {σ} inp fut = num C
  tmp₂ {ix x} {σ} (inp >>> inp₁) fut = (tmp₂ inp (tmp₂ inp₁ fut))
  tmp₂ {δ ⇒ δ₁} {σ ⇒ σ₁} (copy x x₁) fut = ?
  tmp₂ {δ ⇒ δ₁} {σ ⇒ σ₁} (view x inp x₁) fut = ?
  tmp₂ {ix s ⇒ δ} {(ix p) ⇒ σ} (mapi inp) (num (arr x)) = let tmp = tmp₂ inp (num x) in num (arr ?)
  tmp₂ {(ix _) ⇒ C} {.(ar _ C)} (zipw x x₁) fut = fut
  tmp₂ {δ ⇒ δ₁} {_ ⇒ _} (inp >>> inp₁) fut = (tmp₂ inp (tmp₂ inp₁ fut))
  -}

  {-
  tmp : Inp Val δ σ → Fut σ → Fut δ
  tmp {C} {C} (copy _ _) (num C) = num C
  tmp {δ} {C} (inp >>> inp₁) (num C) tmp inp (tmp inp₁ (num C))  = ?
  tmp {δ} {.(ix _ ⇒ _)} inp (num (arr x)) = ?
  tmp {.(ix _) ⇒ _} {.(ar _ _)} (copy (arr _ _) _) (fun () fut)
  tmp {δ ⇒ δ₁} {.(C ⇒ _)} (view x₁ inp x₂) (fun C fut) = ?
  tmp {δ ⇒ δ₁} {.((ix _ ⇒ _) ⇒ _)} (view x₁ inp x₂) (fun (arr x) fut) = ?
  tmp {δ} {.(_ ⇒ _)} (inp >>> inp₁) (fun x fut) = ?
  -}
  {-
  fut-ar : Fut (ar s σ) → Fut σ
  fut-ar (num (arr x)) = num x
  -}

  --data memory (τ : Ty) : Set where
  --  scalar : (var-name : String) → (Fut τ) → memory τ

  -- Yes, I dont need Fut τ and Fut τ as this is inplued by them being in Inp and inp requiring τ ~ σ
  --to-vali : Inp Val τ σ → {- Fut τ → Fut σ → -} (mem : String) → State ℕ (String × Val (τ ⇒ σ))
  {-
  to-val′′ : Inp Val τ σ → {- Fut τ → -} Fut σ → (mem : String) → State ℕ (String × Val (τ ⇒ σ))
  to-val′′ (copy prf expr) fut memAdr = return $ "" , λ v → 
    do
      expr-pre , expr-val ← to-val expr
      expr-app-pre , expr-app ← expr-val v
      tmp ← to-str fut expr-app memAdr  ≔
      return $ memAdr  , expr-app
    {-
    do
      expr-pre , expr-val ← to-val expr
      let tmp = expr-val (` ?)
      return $ printf "%s\nMEMCP(%s INTO %s)" (?) (?) memAdr , expr-val
    -}

  to-val′′ (view T₁ inp T₂) fut memAdr = ?
  to-val′′ (mapi f)       (num (arr x)) memAdr = return $ "" , λ ar → 
    return $ "" , λ i → do
      f-pre , f-val ← to-val′′ f (num x) memAdr
      ar-pre , ar-val ← ar i
      f-ar[i]-pre , f-ar[i]-val ← f-val ar-val
      pre-ass , ass ← to-str (num x) f-ar[i]-val (to-sel i memAdr) ≔
      --let assignment = printf "%s = %s;" (to-sel i memAdr) ? --f-ar[i]-val
      return $ f-pre ++ ar-pre ++ f-ar[i]-pre ++ pre-ass ++ ass , ?
  to-val′′ (zipw {s} ar₁ f) fut memAdr =
    return $ "" , λ ar₂-val →
      return $ "" , λ i → do
        --inner-pre , inner-val ← i i
        --let loop = loop-nest-helper s i (inner-pre ++ inner-val)
        ar₁-pre , ar₁-val ← to-val ar₁
        f-pre , f-val ← to-val f

        ar₁[i]-pre , ar₁[i]-val ← ar₁-val i
        ar₂[i]-pre , ar₂[i]-val ← ar₂-val i

        f-ar₁[i]-pre , f-ar₁[i]-val ← f-val ar₁[i]-val
        f-ar₁[i]-ar₂[i]-pre , f-ar₁[i]-ar₂[i]-val ← f-ar₁[i]-val ar₂[i]-val
        let out-loop-pre = ar₁-pre ++ f-pre
        let inn-loop-pre = ar₁[i]-pre 
                        ++ ar₂[i]-pre 
                        ++ f-ar₁[i]-pre 
                        ++ f-ar₁[i]-ar₂[i]-pre
        let inn-loop-exp = printf "%s = %s;" (to-sel i memAdr) f-ar₁[i]-ar₂[i]-val

        let loop = loop-nest-helper s i (inn-loop-pre ++ inn-loop-exp)
        return $ out-loop-pre ++ loop , memAdr
  to-val′′ (inp₁ >>> inp₂) fut memAdr = 
    do
      inp₁-val-pre , inp₁-val ← to-val′′ inp₁ (?) memAdr
      inp₂-val-pre , inp₂-val ← to-val′′ inp₂ fut memAdr
      return $ "" , λ val → do
        inp₁-app-pre , inp₁-app-val ← inp₁-val val
        inp₂-app-pre , inp₂-app-val ← inp₂-val inp₁-app-val
        return $ (inp₁-val-pre ++ inp₂-val-pre ++ inp₁-app-pre ++ inp₂-app-pre) , inp₂-app-val
        -}

  OOP-T : T τ σ → String → String
  OOP-T idₜ mem = ""
  OOP-T (t ⊡ t₁) mem = (OOP-T t mem) ++ (OOP-T t₁ mem)
  OOP-T (swapₜ {s} {p} {τ = τ}) mem = "//TODO: OOP-T SWAP\n"
  OOP-T nestₜ mem = ""
  OOP-T unnestₜ mem = ""

  {-
  Var : (τ : Ty) → Num τ → Set
  Var C C = String
  Var (ix s ⇒ τ) (arr n) = Ix s → Var τ n

  --cpy : ∀ {m : Num τ} → ∀ {n : Num σ} T τ σ → Var τ m → Var σ n → String
  --cpy = ?

  to-vali-var : ∀ (num : Num τ) → (inp : Inp Val τ σ) → {- Fut τ → Fut σ → -} (mem : Var τ num) → State ℕ (String)
  -- "mem = f mem"
  to-vali-var n (copy sca f) mem = do
    f-pre , f-val ← to-val f
    f-app-pre , f-app ← f-val ?
    return $ f-pre ++ f-app-pre ++ f-app
  to-vali-var n (copy (arr {s} {τ = C} {.C} r sca) f) mem = ?
  to-vali-var n (copy (arr {s} {τ = .(ix _) ⇒ τ₁} {.(ar _ _)} r (arr x prf)) f) mem = ?
  to-vali-var n (view T₁ inp T₂) mem = do
    inp-val ← to-vali-var ? inp ?
    return $ (OOP-T T₁ ?) ++ inp-val ++ (OOP-T T₂ ?)

  -- "for (ix in s) { mem[ix] = f mem[ix] }"
  to-vali-var n (mapi {s = s} inp) mem = do
    i ← generateIx s
    expr ← to-vali-var ? inp ? --(to-sel i mem)
    return $ loop-nest-helper s i expr

  -- "for (ix in s) { mem[ix] = f xs[ix] mem[ix] }"
  to-vali-var n (zipw {s} xs f) mem = do
    ar₁-pre , ar₁ ← to-val xs
    fVal-pre , fVal ← to-val f

    i ← generateIx s

    ar₁-eval-pre , ar₁-eval ← ar₁ i
    f-ar₁-pre , f-ar₁ ← fVal   ar₁-eval
    f-ar₁-ar₂-pre , f-ar₁-ar₂ ← f-ar₁ ? -- (to-sel i mem)

    return $ ar₁-pre 
          ++ fVal-pre 
          ++ ar₁-eval-pre  -- This may need to go inside the loop
          ++ f-ar₁-pre     -- This may need to go inside the loop
          ++ f-ar₁-ar₂-pre -- This may need to go inside the loop
          ++ loop-nest-helper s i (printf "%s = %s;" ? {-(to-sel i mem)-} f-ar₁-ar₂)
  -- "mem = ?; mem = ?"
  to-vali-var n (inp₁ >>> inp₂) mem =
    do
      assignment₁ ← to-vali-var ? inp₁ mem
      assignment₂ ← to-vali-var ? inp₂ ? --mem
      return $ printf "%s%s" assignment₁ assignment₂
  -}

  Var : (τ : Ty) → Num τ → Set
  Var C C = String
  Var (ix s ⇒ τ) (arr n) = Ix s → Var τ n

  to-val-mem : {τ-n : Num τ} → Var τ τ-n → E Val (τ ⇒ σ) → State ℕ (String × Val σ)
  to-val-mem var (` x) = x ?
  to-val-mem var (`lam x) = ?
  to-val-mem var (e `$ e₁) = ?

--`dft : ⦃ NonZero n ⦄ → E V (ar (ι n) C ⇒ ar (ι n) C)
--`dft {n = n} = `λ a ⇒ `λ j ⇒ `sum (`λ k ⇒ (` a `$ ` k) `* `ω n (` k `⊗ ` j))

  toNum : Inp τ σ → Num τ → Num σ
  toNum (e₁ >>> e₂)         n  = toNum e₂ (toNum e₁ n)
  toNum (dft _)        (arr n) = arr n
  toNum twid           (arr n) = arr n
  toNum (part-col _ _) (arr n) = arr n
  toNum (part-row _ _) (arr n) = arr n
  toNum (copy _)       (arr n) = arr n


  --to-vali : (inp : Inp τ σ) → {- Fut τ → Fut σ → -} (mem : String) → State ℕ (String × Val σ)
  --to-vali : (inp : Inp τ σ) → {τ-n : Num τ} {σ-n : Num σ} →{- Fut τ → Fut σ → -} (mem : Var τ τ-n) → State ℕ (String × Var σ σ-n)
  -- mem-To-EVal : {τ-n : Num τ} → Var τ τ-n → E Val τ
  -- mem-To-EVal x = ?

  ~-refl : (τ-n : Num τ) → τ ~ τ
  ~-refl {C}      _   = sca
  ~-refl {ix x} ()
  ~-refl {.(ix _) ⇒ τ₁} (arr τ-n) = arr eq (~-refl τ-n)

  ~-trans : τ ~ σ → σ ~ δ → τ ~ δ
  ~-trans sca sca = sca
  ~-trans (arr rshp₁ r₁) (arr rshp₂ r₂) = arr (rshp₂ ∙ rshp₁) (~-trans r₁ r₂)

  ~-num : τ ~ σ → Num τ → Num σ
  ~-num {σ = C} rel C = C
  ~-num {σ = ix p ⇒ σ} (arr x₁ rel) (arr τ-n) = arr (~-num rel τ-n)

  inp→τ~σ : Inp τ σ → (τ-n : Num τ) →  τ ~ σ
  inp→τ~σ (dft x) _ = arr eq sca
  inp→τ~σ twid _ = arr eq sca
  inp→τ~σ (part-col {τ = τ} x eq) (arr τ-n) = arr eq (~-refl τ-n)
  inp→τ~σ (part-row x eq) (arr τ-n) = arr eq (~-refl τ-n)
  inp→τ~σ (e₁ >>> e₂) τ-n = ~-trans (inp→τ~σ e₁ τ-n) (inp→τ~σ e₂ (toNum e₁ τ-n)) 
  inp→τ~σ (copy x) (arr τ-n) = arr x (~-refl τ-n)

  rshp-ix : Reshape s p → Ix p → Ix s
  rshp-ix eq x₁ = x₁
  rshp-ix (x ∙ x₂) x₁ = (rshp-ix x₂ (rshp-ix x x₁))
  rshp-ix (x ⊕ x₂) (x₁ ⊗ x₃) = (rshp-ix x x₁) ⊗ (rshp-ix x₂ x₃)
  rshp-ix (split {m}) (ι x ⊗ ι x₁) = ι (printf "((%s * %u) * %s)" x m x₁)
  rshp-ix flat (ι x) = ι $ printf "TODO: Flatten"
  rshp-ix Reshape.swap (x₁ ⊗ x₂) = x₂ ⊗ x₁

  convVar : (τ-n : Num τ) → (rel : τ ~ σ) → Var τ τ-n → Var σ (~-num rel τ-n)
  convVar C sca var = var
  convVar (arr τ-n) (arr x rel) var i = convVar τ-n rel $ var $ rshp-ix x i

  --tmp {σ = C} C rel = refl
  --tmp {σ = ix p ⇒ σ} (arr τ-n) (arr x rel) = ?

  to-vali : (inp : Inp τ σ) → {τ-n : Num τ} →{- Fut τ → Fut σ → -} (mem : String) → State ℕ (String × String)
  to-vali (dft {n} nz)     mem =
    do
    --let tmp₁ = `dft {n} {Val} ⦃ nz ⦄
    --tmp₂-pre , tmp₂ ← to-val (?)
    --tmp₃-pre , tmp₃ ← tmp₂ ?
    --return $ tmp₂-pre ++ tmp₃-pre , ?
      let tmp = `λ j ⇒ `sum (`λ k ⇒ (` ? `$ ` k) `* `ω n (` k `⊗ ` j))
      tmp₁-pre , tmp₁ ← to-val $ `dft {V = Val} ⦃ nz ⦄ `$ ?
      --tmp₁ ← to-val (`dft {n})
      let tmp₂ = to-str ? ? ? ≔
      return ?
  to-vali (twid {s})  mem = do 
    i ← generateIx s
    let memSel = (to-sel i mem)
    let loop = loop-nest-helper s i 
    return $ loop (printf "%s *= minus-omega(%u , %s); " memSel (size s) (offset i)) , mem -- , (?) --return $ ? , Var (ar ? C) 
  to-vali (part-col inp x) mem = ?
  to-vali (part-row inp x) mem = ?
  to-vali {τ} {σ} (_>>>_ inp₁ inp₂) {τ-n} mem =
    do
      inp₁-pre , inp₁-var ← to-vali inp₁ mem
      inp₂-pre , inp₂-var ← to-vali inp₂ inp₁-var
      return $ inp₁-pre ++ inp₂-pre , ? --inp₂-var
  to-vali (copy x) {τ-n}   mem =
    do
      --let tmp = convVar τ-n (inp→τ~σ (copy x) τ-n) mem
      return $ ? , ?




  {-
  to-vali : (inp : Inp Val τ σ) → {- Fut τ → Fut σ → -} (mem : String) → State ℕ (String)
  -- "mem = f mem"
  to-vali (copy sca f) mem = do
    f-pre , f-val ← to-val f
    f-app-pre , f-app ← f-val mem
    return $ f-pre ++ f-app-pre ++ f-app
  to-vali (copy (arr {s} {τ = C} {C} r sca) f) mem = do 
    tmp₁ , tmp₂ ← to-val f
    ?


    ?
  to-vali (copy (arr {s} {τ = .(ix _) ⇒ τ₁} {.(ar _ _)} r (arr x prf)) f) mem = ?
  to-vali (view T₁ inp T₂) mem = do
    inp-val ← to-vali inp mem
    return $ (OOP-T T₁ mem) ++ inp-val ++ (OOP-T T₂ mem)

  -- "for (ix in s) { mem[ix] = f mem[ix] }"
  to-vali (mapi {s = s} inp) mem = do
    i ← generateIx s
    expr ← to-vali inp (to-sel i mem)
    return $ loop-nest-helper s i expr

  -- "for (ix in s) { mem[ix] = f xs[ix] mem[ix] }"
  to-vali (zipw {s} xs f) mem = do
    ar₁-pre , ar₁ ← to-val xs
    fVal-pre , fVal ← to-val f

    i ← generateIx s

    ar₁-eval-pre , ar₁-eval ← ar₁ i
    f-ar₁-pre , f-ar₁ ← fVal   ar₁-eval
    f-ar₁-ar₂-pre , f-ar₁-ar₂ ← f-ar₁ (to-sel i mem)

    return $ ar₁-pre 
          ++ fVal-pre 
          ++ ar₁-eval-pre  -- This may need to go inside the loop
          ++ f-ar₁-pre     -- This may need to go inside the loop
          ++ f-ar₁-ar₂-pre -- This may need to go inside the loop
          ++ loop-nest-helper s i (printf "%s = %s;" (to-sel i mem) f-ar₁-ar₂)
  -- "mem = ?; mem = ?"
  to-vali (inp₁ >>> inp₂) mem =
    do
      assignment₁ ← to-vali inp₁ mem
      assignment₂ ← to-vali inp₂ mem
      return $ printf "%s%s" assignment₁ assignment₂
  -}
  {-
  to-val′′ : Inp Val τ σ → {- Fut τ → -} Fut σ → (mem : String) → State ℕ (String × Val (τ ⇒ σ))
  to-val′′ (copy prf expr) fut memAdr = return $ "" , λ v → 
    do
      expr-pre , expr-val ← to-val expr
      expr-app-pre , expr-app ← expr-val v
      tmp ← to-str fut expr-app memAdr  ≔
      return $ memAdr  , expr-app
    {-
    do
      expr-pre , expr-val ← to-val expr
      let tmp = expr-val (` ?)
      return $ printf "%s\nMEMCP(%s INTO %s)" (?) (?) memAdr , expr-val
    -}
  to-val′′ (view T₁ inp T₂) fut memAdr = ?
  to-val′′ (mapi f)       (num (arr x)) memAdr = return $ "" , λ ar → 
    return $ "" , λ i → do
      f-pre , f-val ← to-val′′ f (num x) memAdr
      ar-pre , ar-val ← ar i
      f-ar[i]-pre , f-ar[i]-val ← f-val ar-val
      pre-ass , ass ← to-str (num x) f-ar[i]-val (to-sel i memAdr) ≔
      --let assignment = printf "%s = %s;" (to-sel i memAdr) ? --f-ar[i]-val
      return $ f-pre ++ ar-pre ++ f-ar[i]-pre ++ pre-ass ++ ass , ?
  to-val′′ (zipw {s} ar₁ f) fut memAdr =
    return $ "" , λ ar₂-val →
      return $ "" , λ i → do
        --inner-pre , inner-val ← i i
        --let loop = loop-nest-helper s i (inner-pre ++ inner-val)
        ar₁-pre , ar₁-val ← to-val ar₁
        f-pre , f-val ← to-val f

        ar₁[i]-pre , ar₁[i]-val ← ar₁-val i
        ar₂[i]-pre , ar₂[i]-val ← ar₂-val i

        f-ar₁[i]-pre , f-ar₁[i]-val ← f-val ar₁[i]-val
        f-ar₁[i]-ar₂[i]-pre , f-ar₁[i]-ar₂[i]-val ← f-ar₁[i]-val ar₂[i]-val
        let out-loop-pre = ar₁-pre ++ f-pre
        let inn-loop-pre = ar₁[i]-pre 
                        ++ ar₂[i]-pre 
                        ++ f-ar₁[i]-pre 
                        ++ f-ar₁[i]-ar₂[i]-pre
        let inn-loop-exp = printf "%s = %s;" (to-sel i memAdr) f-ar₁[i]-ar₂[i]-val

        let loop = loop-nest-helper s i (inn-loop-pre ++ inn-loop-exp)
        return $ out-loop-pre ++ loop , memAdr
  to-val′′ (inp₁ >>> inp₂) fut memAdr = 
    do
      inp₁-val-pre , inp₁-val ← to-val′′ inp₁ (?) memAdr
      inp₂-val-pre , inp₂-val ← to-val′′ inp₂ fut memAdr
      return $ "" , λ val → do
        inp₁-app-pre , inp₁-app-val ← inp₁-val val
        inp₂-app-pre , inp₂-app-val ← inp₂-val inp₁-app-val
        return $ (inp₁-val-pre ++ inp₂-val-pre ++ inp₁-app-pre ++ inp₂-app-pre) , inp₂-app-val
  -}
  --
  --to-val′ (copy x x₁) adr = ?
  --to-val′ (view x x₁ x₂) adr = ?
  --to-val′ (mapi f) adr = return $ ? ,
  --  (λ i → do
  --    tmp₁ , tmp₂ ← to-val′ f adr
  --    ?
  --  )
  --to-val′ (zipw x x₁) adr = ?
  --to-val′ (x >>> x₁) adr = ?
  {-
  to-val′ (copy sca e) adr = do
    let e-app = e `$ ` adr 
    pre , val ← to-val e-app
    return $ (printf "%s\nCOPY(%s INTO %s)" pre val adr) , ?
    ?
  to-val′ tmp@(copy (arr x x₂) e) adr = do
    let tmp = e `$ ` ?
    ?
  to-val′ (view x x₁ x₂)       adr = do
    ?
  to-val′ (mapi x)             adr = ?
  to-val′ (zipw x x₁)          adr = ?
  to-val′ (ie₁ >>> ie₂)        adr = do
    pre₁ ← to-val′ ie₁ adr
    ?
  -}
{-

  --reuse a  ((swap ∘ unnest) ∘ (map inc) ∘ view (nest ∘ swap a))

  reuse a (view r e) => reuse (view (rev r) a) e
  reuse a (map f e)  => for i in a: reuse (a $ i) (e $ i)
  reuse a (view r b) => for i in a: reuse (a $ i) (b $ (rev r))

  a: [m,n]

  for i < n:
    t = f (λ k → a (k, i))
    for j < m
      a[j,i] = t[j]


-}


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

  --show′ : (Inp τ σ) → String → String
  --show′ e res = runState (
  --    do
  --      val ← to-vali e res
  --      return $ val
  --  ) 0 .proj₂

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

  --fft : (s : Shape) → ⦃ NonZeroₛ s ⦄ → Inp _ _
  --fft s = `ffti {s = s}

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

  --gen-dft : (n : ℕ) → ⦃ _ : NonZero n ⦄ → String × String
  --gen-dft n with show-test "dft" (dft n) _ 
  --... | head , body = preamble ++ head , preamble ++ body

  --res : String × String
  --res = show-test "test" fft-mini _

--open Tests using (gen-fft; gen-dft) public

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

