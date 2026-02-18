open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Fin as Fin
open import Data.Bool
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong)
open Eq.≡-Reasoning
open import Function
open import Algebra.Definitions

open import Data.Unit
-- This gives a warn on older versions of Agda when Product doesnt have a zipWith method
open import Data.Product hiding (swap; map; map₁; map₂; zipWith)

open import Complex using (Cplx)

module _ (cplx : Cplx) where

open Cplx cplx using (ℂ) renaming (_*_ to _*ᶜ_)

--postulate
--  ℂ : Set
--  _*ᶜ_ : ℂ → ℂ → ℂ

infixl 4 _⊡_
_⊡_ = trans


record Mon : Set₁ where
  field
    U : Set
    El : U → Set

    -- ι : U
    -- _⊗_ : U → U → U

    -- unit-law : El ι ↔ ⊤
    -- -- The bracketing on the left hand side here is VERY important, otherwise
    -- -- we have a pair where the left is an isomorhism... that took me too long
    -- pair-law : ∀ a b → El (a ⊗ b) ↔ (El a × El b)

    -- comm : ∀ a b → a ⊗ b ≡ b ⊗ a

{-
record Uops (U : Set) (El : U → Set) : Set where
  field
    sum : ∀ u → (El u → ℂ) → ℂ
    -ω : U → ℂ → ℂ
-}

record Uops (M : Mon) : Set where
  open Mon M 

  field
    sum : ∀ u → (El u → ℂ) → ℂ
    -ω : U → ℂ → ℂ

--module A (U : Set) (El : U → Set) where
module A (M : Mon) where
  open Mon M using (U; El) --; pair-law) renaming (ι to ι′; _⊗_ to _⊗′_; comm to ⊗′-comm)

  --open import Function.Properties.Inverse using (toFunction; fromFunction)

  --private
  --  to : ∀ (a b : U) → (El (a ⊗′ b)) → (El a × El b)
  --  to a b = Inverse.to $ pair-law a b

  infixl 15 _⊗_
  data S : Set where
    ι : U → S  --  ι n means ι (suc n)
    _⊗_ : S → S → S

  variable
    s s′ p q q₁ q₂ r V : S
    m n k : U
    X Y Z : Set

  data P : S → Set where
    ι : El n → P (ι n)
    _⊗_ : P s → P p → P (s ⊗ p)

  Ar : S → Set → Set
  Ar s X = P s → X

  infixl 5 _∙_
  data Reshape : S → S → Set where
    eq : Reshape s s
    _⊕_ : Reshape s p → Reshape q r → Reshape (s ⊗ q) (p ⊗ r)
    _∙_ : Reshape p q → Reshape s p → Reshape s q
    swap : Reshape (s ⊗ p) (p ⊗ s)
    assocl : Reshape (s ⊗ (p ⊗ q)) ((s ⊗ p) ⊗ q)
    assocr : Reshape ((s ⊗ p) ⊗ q) (s ⊗ (p ⊗ q))

    --flat : Reshape (ι m ⊗ ι n) (ι (m ⊗′ n)) 
    --unflat : Reshape (ι (m ⊗′ n)) (ι m ⊗ ι n)

  _⟨_⟩ : P s → Reshape p s → P p
  i ⟨ eq ⟩ = i
  (i ⊗ i₁) ⟨ r ⊕ r₁ ⟩ = (i ⟨ r ⟩) ⊗ (i₁ ⟨ r₁ ⟩)
  i ⟨ r ∙ r₁ ⟩ = (i ⟨ r ⟩) ⟨ r₁ ⟩
  (i ⊗ i₁) ⟨ swap ⟩ = i₁ ⊗ i
  ((i ⊗ j) ⊗ k) ⟨ assocl ⟩ = i ⊗ (j ⊗ k)
  (i ⊗ (j ⊗ k)) ⟨ assocr ⟩ = (i ⊗ j) ⊗ k

  --ι x ⟨ flat ⟩ = let a = (Inverse.to $ pair-law _ _) x in ι (proj₁ a) ⊗ ι (proj₂ a)
  --(ι x₁ ⊗ ι x₂) ⟨ unflat ⟩ = ι ((Inverse.from $ pair-law _ _) (x₁ , x₂))

  rev : Reshape s p → Reshape p s
  rev eq = eq
  rev (r₁ ⊕ r₂) = (rev r₁) ⊕ (rev r₂)
  rev (r₁ ∙ r₂) = (rev r₂) ∙ (rev r₁)
  rev swap = swap
  rev assocl = assocr
  rev assocr = assocl

  --rev unflat = flat
  --rev flat = unflat

  rev-rev : ∀ (r : Reshape s p) (i : P p) →  i ⟨ r ∙ rev r ⟩ ≡ i
  rev-rev eq i = refl
  rev-rev (r₁ ⊕ r₂) (i₁ ⊗ i₂) rewrite rev-rev r₁ i₁ | rev-rev r₂ i₂ = refl
  rev-rev (r₁ ∙ r₂) i rewrite rev-rev r₂ (i ⟨ r₁ ⟩) | rev-rev r₁ i  = refl
  rev-rev swap (i₁ ⊗ i₂) = refl
  rev-rev assocl (i₁ ⊗ i₂ ⊗ i₃) = refl
  rev-rev assocr (i₁ ⊗ (i₂ ⊗ i₃)) = refl
  --rev-rev unflat (ι {m} x₁ ⊗ ι {n} x₂) 
  --  rewrite
  --    (proj₁ ((Inverse.inverse (pair-law m n))) {x₁ , x₂}) refl 
  --  = refl
  --rev-rev (flat {m} {n}) (ι x)
  --  rewrite
  --    (proj₂ ((Inverse.inverse (pair-law m n))) {x}) refl 
  --  = refl

  rev-rev′ : ∀ (r : Reshape s p) (i : P s) →  i ⟨ rev r ∙ r ⟩ ≡ i
  rev-rev′ eq i = refl
  rev-rev′ (r₁ ⊕ r₂) (i₁ ⊗ i₂) rewrite rev-rev′ r₁ i₁ | rev-rev′ r₂ i₂ = refl
  rev-rev′ (r₁ ∙ r₂) i rewrite rev-rev′ r₁ (i ⟨ rev r₂ ⟩) | rev-rev′ r₂ i = refl
  rev-rev′ swap (i₁ ⊗ i₂) = refl
  rev-rev′ assocl (i₁ ⊗ (i₂ ⊗ i₃)) = refl
  rev-rev′ assocr (i₁ ⊗ i₃ ⊗ i₂)   = refl
  --rev-rev′ (unflat {m} {n}) (ι x)
  --  rewrite
  --    (proj₂ ((Inverse.inverse (pair-law m n))) {x}) refl 
  --  = refl
  --rev-rev′ (flat {m} {n}) (ι x₁ ⊗ ι x₂)
  --  rewrite
  --    (proj₁ ((Inverse.inverse (pair-law m n))) {x₁ , x₂}) refl 
  --  = refl

  --reindex : m ≡ n → Reshape (ι m) (ι n)
  --reindex {m} {n} prf = subst (λ t → Reshape (ι m) (ι t)) prf eq

  reshape : Reshape s p → Ar s X → Ar p X
  reshape r a i = a (i ⟨ r ⟩)

  --size : S → U
  --size (ι x) = x
  --size (s₁ ⊗ s₂) = size s₁ ⊗′ size s₂

  --♭ : Reshape s (ι (size s))
  --♭ {ι x} = eq
  --♭ {s₁ ⊗ s₂} = flat ∙ ♭ ⊕ ♭

  transp : S → S
  transp (ι n) = ι n
  transp (s ⊗ p) = transp p ⊗ transp s

  transpᵣ : Reshape (transp s) s
  transpᵣ {ι x} = eq
  transpᵣ {s ⊗ s₁} = (transpᵣ ⊕ transpᵣ) ∙ swap

  --|s|≡|sᵗ| : ∀ s → size s ≡ size (transp s)
  --|s|≡|sᵗ| (ι x) = refl
  --|s|≡|sᵗ| (s₁ ⊗ s₂) rewrite
  --    |s|≡|sᵗ| s₁
  --  | |s|≡|sᵗ| s₂
  --  | ⊗′-comm (size (transp s₁)) (size (transp s₂))
  --  = refl

  map : (X → Y) → Ar s X → Ar s Y
  map f a i = f (a i)

  imap : (P s → X → Y) → Ar s X → Ar s Y
  imap f a i = f i (a i)

  zipWith : (X → Y → Z) → Ar s X → Ar s Y → Ar s Z
  zipWith _⊡_ a b i = a i ⊡ b i

  nest : Ar (s ⊗ p) X → Ar s (Ar p X)
  nest a i j = a (i ⊗ j)

  unnest : Ar s (Ar p X) → Ar (s ⊗ p) X
  unnest a (i ⊗ j) = a i j

  map-reshape : ∀ (f : X → Y)
              → ∀ (r : Reshape s p)
              → ∀ (xs : Ar s X)
              → ∀ i
              → map f xs i ≡ reshape (rev r) (map f (reshape r xs)) i
  map-reshape f r xs i rewrite rev-rev′ r i = refl

  map-nest : ∀ (f : X → Y)
             → ∀ (xs : Ar (s ⊗ p) X)
             → ∀ i
             → map f xs i ≡ unnest (map (map f) (nest xs)) i
  map-nest f xs (i₁ ⊗ i₂) = refl

  map-assoc : ∀ (f : X → Y)
            → ∀ (xs : Ar ((s ⊗ p) ⊗ q) X)
            → ∀ i
            → map f xs i ≡ (reshape assocl
                              (unnest (map (map f) (nest (reshape assocr xs))))
                           ) i
  map-assoc f xs i@((i₁ ⊗ i₂) ⊗ i₃) = refl

  reshape-cong  : ∀ (r : Reshape s p)
                → ∀ {a b : Ar s X}
                → (∀ i → a i ≡ b i)
                → ∀ (i : P p) 
                → reshape r a i ≡ reshape r b i
  reshape-cong r x i = x (i ⟨ r ⟩)

  resh-rev : (r : Reshape s p) → ∀ i → i ⟨ rev r ⟩ ⟨ r ⟩ ≡ i
  resh-rev eq i = refl
  resh-rev (r ⊕ r₁) (i ⊗ j) rewrite resh-rev r i | resh-rev r₁ j = refl
  resh-rev (r ∙ r₁) i rewrite resh-rev r (i ⟨ rev r₁ ⟩) = resh-rev r₁ i
  resh-rev swap (i ⊗ j) = refl
  resh-rev assocl (i ⊗ (i₁ ⊗ i₂)) = refl
  resh-rev assocr (i ⊗ i₂ ⊗ i₁) = refl

  resh-rev-transpᵣ : ∀ { s } → ∀ i → i ⟨ rev transpᵣ ⟩ ⟨ transpᵣ {s} ⟩ ≡ i
  resh-rev-transpᵣ {ι n} (ι x) = refl
  resh-rev-transpᵣ {s ⊗ p} (i ⊗ j) rewrite
      resh-rev-transpᵣ i
    | resh-rev-transpᵣ j
    = refl
 
  rev-fact : (r : Reshape s p) → ∀ i j → i ⟨ rev r ⟩ ≡ j → i ≡ j ⟨ r ⟩
  rev-fact r i j e = sym (resh-rev r i) ⊡ cong (_⟨ r ⟩) e

--module D (U : Set) (El : U → Set) where
module D (M : Mon)  where
  open Mon M using (U; El)
  open A M

  -- All of these should be defined through
  -- the corresponfing functions in U ◃ El universe
  sum : Ar s ℂ → ℂ
  -ω : U → ℂ → ℂ
  iota : P s → ℂ
  size : S → U


  dft : Ar (ι n) ℂ → Ar (ι n) ℂ
  dft {n} a j = sum (λ k → a k *ᶜ -ω n (iota k *ᶜ iota j))

  twiddles : P s → P p → ℂ
  twiddles {s} {p} i j = -ω (size (s ⊗ p)) (iota i *ᶜ iota j)


--module F (U : Set) (El : U → Set) where
module F (M : Mon)  where
  open Mon M using (U; El)
  open A M

  -- Parametrised (u)ffts
  fft : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
        (twid : ∀ {s p} → P s → P p → ℂ)
      → Ar s ℂ → Ar (transp s) ℂ
  fft {s = ι n} dft twid = dft
  fft {s = s ⊗ p} dft twid a =
    let 
      b = map (fft dft twid) (nest (reshape swap a))
      c = unnest (λ i → zipWith _*ᶜ_ (twid i) (b i)) 
      d = map (fft dft twid) (nest (reshape swap c))
    in reshape swap (unnest d)

  -----------------------------------------------------------------------------

  ufft : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
         (twid : ∀ {s p} → P s → P p → ℂ)
       → Ar s ℂ → Ar s ℂ
  ufft {A.ι n} dft twid = dft
  ufft {s A.⊗ p} dft twid a =
    let 
      c = unnest $ imap 
          (λ i → zipWith _*ᶜ_ (twid {p} {s} i) ∘ ufft {s} dft twid) 
        (nest (reshape swap a))
      d = map (ufft {p} dft twid) (nest (reshape swap c))
    in (unnest d)
  
  pre-ufft : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
         (twid : ∀ {s p} → P s → P p → ℂ)
       → Ar s ℂ → Ar s ℂ
  pre-ufft {A.ι n} dft twid = dft
  pre-ufft {s A.⊗ p} dft twid a =
    let 
      c = unnest $ imap 
          (λ i → zipWith _*ᶜ_ (twid {s} {p} i) ∘ pre-ufft {p} dft twid) 
        (nest a)
      d = map (pre-ufft {s} dft twid) (nest (reshape swap c))
    in reshape swap (unnest d)

  -----------------------------------------------------------------------------
  -- Vectorisable shape components
  -- [m , n] => ∃ k . kv = m

  data VEC (V : S) : S → Set where
    -- XXX: probably ok, but we need more powerful reshape
    ι : Reshape (ι n) (s ⊗ V) → VEC V (ι n)
    _⊗_ : VEC V s → VEC V p → VEC V (s ⊗ p)

  pull-V : VEC V s → S
  pull-V {_} {.(ι _)} (ι {s = s} _) = s
  pull-V {_} {(s ⊗ _)} (_ ⊗ vec) = s ⊗ (pull-V vec)

  pull-Vᵣ : (vec : VEC V s) → Reshape s ((pull-V vec) ⊗ V)
  pull-Vᵣ {_} {.(ι _)} (ι r) = r
  pull-Vᵣ {V} {.(_ ⊗ _)} (_ ⊗ vec) = assocl ∙ eq ⊕ (pull-Vᵣ vec)

  vec-fst : VEC V (s ⊗ p) → VEC V s
  vec-fst (a ⊗ _) = a

  {-
  This defines the general pattern we wish to use for iterating over a 
  vectorised shape (s ⊗ p), where:
    - f is defined as a vectorised operation which we wish to run over the 
      leaves of our shape
    - g and g′ are the functions we wish to run when at a non leaf node, where
      g is ran over the left hand sub shape, and g′ is ran over the entire
      tree s ⊗ p.
      g and g′ both accept an instance of the VEC predicate as to allow them to 
      define their own vectorisations (i.e. it allows g and g′ to be vectorised
      functions without direct restriction on their shape as we have for f)
  -}
  vecPattern : (vec : VEC V (s ⊗ p))
              --→ (f  : ∀ {n}                            → Ar (V ⊗ ι n) X → Ar (V ⊗ ι n) Y)
              → (f  : ∀ {n} → P (pull-V (vec-fst vec)) → Ar (V ⊗ ι n) X → Ar (V ⊗ ι n) Z)
              → (g  : VEC V      p  → Ar p X       → Ar p Y      )
              → (g′ : VEC V (s ⊗ p) → Ar (s ⊗ p) Y → Ar (s ⊗ p) Z) 
              → Ar (s ⊗ p) X
              → Ar (s ⊗ p) Z
  vecPattern vec@(vec₁ ⊗ ι _) f _ h xs =
    let
      a = nest $ reshape (assocr ∙ pull-Vᵣ vec₁ ⊕ eq) xs
      b = imap f a
      c = reshape (rev (assocr ∙ pull-Vᵣ vec₁ ⊕ eq)) (unnest b)
    in c
  vecPattern vec@(_ ⊗ (vec₂ ⊗ vec₃)) _ g g′ xs =
      g′ vec $ unnest $ map (g (vec₂ ⊗ vec₃)) (nest xs)
  
  id₁ : X → Y → Y
  id₁ = λ _ → id


  -- We want to trainsition away from copying this out in the form
  -- V ⊗ s, and instead copy out sᵗ ⊗ V
  -- First step -- 
  dftVec :  (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ) 
            → Ar (V ⊗ ι n) ℂ
            → Ar (V ⊗ ι n) ℂ
  dftVec dft xs = unnest (map dft (nest xs))

  ufft-vec₁ : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
         (twid : ∀ {s p} → P s → P p → ℂ)
       → VEC V s
       → Ar s ℂ → Ar s ℂ

  ufft-vec₁ {V} {A.ι n  } dft twid vec = dft
  ufft-vec₁ {V} {s A.⊗ p} dft twid (vec₁ ⊗ vec₂) a =
    let 
      --b = nest $ mapVec₁ dft (ufft-vec₁ dft twid) (vec₂ ⊗ vec₁) (reshape swap a)
      b = nest $ vecPattern 
                    (vec₂ ⊗ vec₁) 
                    (λ _ → (dftVec dft)) 
                    (ufft-vec₁ dft twid) 
                    id₁ 
                    (reshape swap a)
      c = unnest (λ i → zipWith _*ᶜ_ (twid i) (b i)) 
      --d = mapVec₁ dft (ufft-vec₁ dft twid) (vec₁ ⊗ vec₂) (reshape swap c)
      d = vecPattern
                    (vec₁ ⊗ vec₂)
                    (λ _ → (dftVec dft)) 
                    (ufft-vec₁ dft twid) 
                    id₁ 
                    (reshape swap c)
    in d

  -----------------------------------------------------------------------------

  -- Ideally I'd like to rewrite this with the vecPattern, but this 
  -- doesn't seem to play too nicely with some of the rewrites which follow it,
  -- I wonder if this is because vecPattern matches over vec₂ while we don't 
  -- need to here, meaning the rewrites don't know which case to operate on and
  -- getting them stuck
  -- May come back to this, but not a current priority
  mapTwid₂ : (twid : ∀ {s p} → P s → P p → ℂ)
           → VEC V (s ⊗ p)
           → Ar (s ⊗ p) ℂ
           → Ar (s ⊗ p) ℂ
  --mapTwid₂ twid (vec₁ ⊗ vec₂) xs =
  --   vecPattern (vec₁ ⊗ vec₂) ? id₁ ? xs
  mapTwid₂ {V} {s} {p} twid (vec₁ ⊗ vec₂) xs = let
      a = nest $ reshape (assocr ∙  (pull-Vᵣ vec₁ ⊕ eq)) xs
      b = imap (λ i → zipWith _*ᶜ_ (λ j → (unnest (twid {s} {p})) ((i ⊗ j) ⟨ assocr ∙ (pull-Vᵣ vec₁ ⊕ eq) ⟩ ))) a
      c = reshape (rev (assocr ∙  (pull-Vᵣ vec₁ ⊕ eq))) (unnest b)
    in c

  mapTwid₂-prop : ∀ (twid : ∀ {s p} → P s → P p → ℂ)
           → ∀ (vec : VEC V (s ⊗ p))
           → ∀ (xs : Ar (s ⊗ p) ℂ)
           → ∀ (i : P (s ⊗ p)) → (mapTwid₂ twid vec xs) i ≡ (zipWith _*ᶜ_ (unnest twid) xs) i
  mapTwid₂-prop twid (vec₁ ⊗ vec₂) xs (i₁ A.⊗ i₂)
    with (i₁ ⟨ rev (pull-Vᵣ vec₁) ⟩) | Eq.inspect (i₁ ⟨_⟩) (rev (pull-Vᵣ vec₁))
  ... | k ⊗ l | Eq.[ e ] rewrite sym (rev-fact (pull-Vᵣ vec₁) _ _ e) = refl


  ufft-vec₂ : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
         (twid : ∀ {s p} → P s → P p → ℂ)
       → VEC V s
       → Ar s ℂ → Ar s ℂ
  ufft-vec₂ {V} {A.ι n  } dft twid vec = dft
  ufft-vec₂ {V} {s A.⊗ p} dft twid (vec₁ ⊗ vec₂) a =
    let 
      b = vecPattern 
            (vec₂ ⊗ vec₁) 
            (λ _ → (dftVec dft)) 
            (ufft-vec₂ dft twid) 
            id₁ 
            (reshape swap a)
      c = mapTwid₂ twid (vec₂ ⊗ vec₁) b
      d = vecPattern
            (vec₁ ⊗ vec₂)
            (λ _ → (dftVec dft)) 
            (ufft-vec₂ dft twid) 
            id₁ 
            (reshape swap c)
    in d

  -----------------------------------------------------------------------------
  ufft-vec₃ : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
         (twid : ∀ {s p} → P s → P p → ℂ)
       → VEC V s
       → Ar s ℂ → Ar s ℂ

  mapVec₃ : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
           (twid : ∀ {s p} → P s → P p → ℂ)
           → (twiddle? : Bool)
           → VEC V (s ⊗ p)
           → Ar (s ⊗ p) ℂ 
           → Ar (s ⊗ p) ℂ
  mapVec₃ {V} {s} {p} dft twid twiddle? vec@(vec₁ ⊗ _) xs =
          vecPattern 
            vec 
            ( 
              if twiddle? then 
                (λ i x → 
                  zipWith 
                    _*ᶜ_ 
                    (λ j → (unnest (twid {s})) ((i ⊗ j) ⟨ assocr ∙ (pull-Vᵣ vec₁ ⊕ eq) ⟩ )) 
                    (dftVec dft x)
                )
              else 
                (λ _ → dftVec dft)
            )
            (ufft-vec₃ dft twid)
            (if twiddle? then mapTwid₂ twid else id₁)
            xs

  ufft-vec₃ {V} {A.ι n  } dft twid vec = dft
  ufft-vec₃ {V} {s A.⊗ p} dft twid (vec₁ ⊗ vec₂) a =
    let 
      b = mapVec₃ dft twid true  (vec₂ ⊗ vec₁) (reshape swap a)
      c = mapVec₃ dft twid false (vec₁ ⊗ vec₂) (reshape swap b)
    in c
  -----------------------------------------------------------------------------

  fft-cong : {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
              {twid : ∀ {s p} → P s → P p → ℂ}
            → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                        → ∀ i → dft {n} a i ≡ dft b i)
            → ∀ {s} a b → (∀ i → a i ≡ b i)
            → ∀ i → fft {s} dft twid a i ≡ fft dft twid b i
  fft-cong dft-cong {A.ι x} a b a≡b i = dft-cong a b a≡b i
  fft-cong dft-cong {s A.⊗ p} a b a≡b (i A.⊗ j) = fft-cong 
        dft-cong _ _
        (λ k → cong (_ *ᶜ_) 
                    (fft-cong 
                        dft-cong _ _ 
                        (λ l → a≡b (l ⊗ k))
                        j))
        i

  ufft-cong : {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
              {twid : ∀ {s p} → P s → P p → ℂ}
            → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                        → ∀ i → dft {n} a i ≡ dft b i)
            → ∀ {s} a b → (∀ i → a i ≡ b i)
            → ∀ i → ufft {s} dft twid a i ≡ ufft dft twid b i
  ufft-cong dft-cong {A.ι x} a b a≡b i = dft-cong a b a≡b i
  ufft-cong dft-cong {s A.⊗ p} a b a≡b (i A.⊗ j) 
    = ufft-cong 
        dft-cong _ _
        (λ k → cong (_ *ᶜ_) 
                    (ufft-cong 
                        dft-cong _ _ 
                        (λ l → a≡b (l ⊗ k))
                        i))
        j

  pre-ufft-cong : {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
              {twid : ∀ {s p} → P s → P p → ℂ}
            → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                        → ∀ i → dft {n} a i ≡ dft b i)
            → ∀ {s} a b → (∀ i → a i ≡ b i)
            → ∀ i → pre-ufft {s} dft twid a i ≡ pre-ufft dft twid b i
  pre-ufft-cong dft-cong a b prf i@(A.ι _) = dft-cong a b prf i
  pre-ufft-cong dft-cong a b prf (i₁ A.⊗ i₂) =
    pre-ufft-cong dft-cong _ _ 
      (λ j₁ → 
        cong₂ _*ᶜ_ 
          refl 
          (pre-ufft-cong dft-cong _ _ (λ j₂ → prf (j₁ ⊗ j₂)) i₂)
      ) i₁
  
  ufft≡fft :   ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
             → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
             → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                         → ∀ i → dft {n} a i ≡ dft b i)
             → ∀ (xs : Ar s ℂ)
             → ∀ (i : P s) 
             →  ufft dft (λ i j → twid i (j ⟨ transpᵣ ⟩)) xs i
                ≡ 
                reshape (A.transpᵣ M) (fft  dft twid xs) i --((A._⟨_⟩ M i (A.transpᵣ M)))
                --fft  dft twid xs ((A._⟨_⟩ M i (A.transpᵣ M)))
  ufft≡fft _ _ (A.ι _) = refl
  ufft≡fft dft-cong xs (i₁ A.⊗ j₁) = 
      (ufft-cong dft-cong _ _ (λ i₂ → cong₂ _*ᶜ_ refl (ufft≡fft dft-cong _ i₁)) j₁)
      ⊡
      (ufft≡fft dft-cong _ j₁)

  pre-ufft≡fft′ :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                 → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                 → (transp-twid : ∀ {s p} → ∀ {i j} → twid ((i ⟨ transpᵣ ⟩) ⟨ transpᵣ ⟩) j ≡ twid {s} {p} i j)
                 → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                             → ∀ i → dft {n} a i ≡ dft b i)
                 → ∀ (xs : Ar s ℂ)
                 → ∀ (ys : Ar (transp s) ℂ)
                 → (prf : ∀ i → ys (i ⟨ transpᵣ ⟩) ≡ xs i)
                 → ∀ (i : P (transp s)) 
                 →  (pre-ufft dft (λ i₁ j₁ → twid (i₁ ⟨ transpᵣ ⟩) j₁ ) ys) i
                    ≡ 
                    fft dft twid xs i
  pre-ufft≡fft′ {A.ι x} transp-twid dft-cong xs ys prf = dft-cong ys xs prf
  pre-ufft≡fft′ {s₁ A.⊗ s₂} {_} {twid} transp-twid dft-cong xs ys prf (i₁ A.⊗ i₂) =
      pre-ufft≡fft′ transp-twid dft-cong _ _ 
        (λ j₁ → 
          cong₂ _*ᶜ_ 
            transp-twid --(cong₂ twid ? refl)
            (pre-ufft≡fft′ transp-twid dft-cong _ _ (λ j₂ → prf (j₂ ⊗ j₁)) i₂)
        )
        i₁

  pre-ufft≡fft :   ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
             → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
             → (transp-twid : ∀ {s p} → ∀ {i j} → twid ((i ⟨ transpᵣ ⟩) ⟨ transpᵣ ⟩) j ≡ twid {s} {p} i j)
             → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                         → ∀ i → dft {n} a i ≡ dft b i)
             → ∀ (xs : Ar s ℂ)
             → ∀ (i : P (transp s)) 
             →  (pre-ufft dft (λ i₁ j₁ → twid (i₁ ⟨ transpᵣ ⟩) j₁ ) (reshape (rev transpᵣ) xs)) i
                ≡ 
                (fft  dft twid xs) i
  pre-ufft≡fft transp-twid dft-cong xs i = pre-ufft≡fft′ transp-twid dft-cong xs (reshape (rev transpᵣ) xs) (cong xs ∘ rev-rev transpᵣ) i

  pre-ufft≡post-ufft :
               ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
             → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
             → (transp-twid : ∀ {s p} → ∀ {i j} → twid ((i ⟨ transpᵣ ⟩) ⟨ transpᵣ ⟩) j ≡ twid {s} {p} i j)
             → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                         → ∀ i → dft {n} a i ≡ dft b i)
             → ∀ (xs : Ar s ℂ)
             → ∀ (i : P (transp s)) 
             → pre-ufft dft (λ j₁ j₂ → twid (j₁ ⟨ transpᵣ ⟩) j₂) (reshape (rev transpᵣ) xs) i
                 ≡
               reshape (rev transpᵣ) (ufft dft (λ j₁ j₂ → twid j₁ (j₂ ⟨ transpᵣ ⟩)) xs) i
  pre-ufft≡post-ufft {s} {dft} {twid} transp-twid dft-cong xs i =
      pre-ufft≡fft {_} {dft} {twid} transp-twid dft-cong xs i
    ⊡ cong (fft dft twid xs) (sym (rev-rev′ transpᵣ i))
    ⊡ sym (ufft≡fft {_} {dft} {twid} dft-cong xs (i ⟨ rev transpᵣ ⟩))

            {-
            FM.pre-ufft dft (λ j₁ → twiddles (j₁ ⟨ transpᵣ₁ ⟩₁))
            (λ i → xs (ι₁ (i ⟨ rev₁ transpᵣ₁ ⟩₁))) (x ⟨ change-major ⟩₁)
            ≡
            FM.ufft dft (λ i j → twiddles i (j ⟨ transpᵣ₁ ⟩₁))
            (λ i → ys (ι₁ i)) ((x ⟨ transpᵣ₁ ⟩₁) ⟨ rev₁ transpᵣ₁ ⟩₁)
            -}

  mapVec₁ : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
           → (ufft-vec : VEC V p → Ar p ℂ → Ar p ℂ)
           → VEC V (s ⊗ p)
           → Ar (s ⊗ p) ℂ 
           → Ar (s ⊗ p) ℂ
  mapVec₁ {V} dft ufft-vec vec xs = vecPattern vec (λ _ → (dftVec dft)) ufft-vec id₁ xs
  -----------------------------------------------------------------------------

  map-vec₁≡map-ufft :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                    → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                    → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                                → ∀ i → dft {n} a i ≡ dft b i)
                    → ∀ (vec : VEC V (s ⊗ p))
                    → ∀ (xs : Ar (s ⊗ p) ℂ)
                    → ∀ (i : P (s ⊗ p)) 
                    → mapVec₁ dft (ufft-vec₁ dft twid) vec xs i ≡ unnest (map (ufft dft twid) (nest xs)) i

  ufft-vec₁≡ufft :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                  → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                  → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                              → ∀ i → dft {n} a i ≡ dft b i)
                  → ∀ (vec : VEC V s)
                  → ∀ (xs : Ar s ℂ)
                  → ∀ (i : P s) 
                  →  ufft-vec₁ dft twid vec xs i
                     ≡ 
                     ufft dft twid xs i

  map-vec₁≡map-ufft dft-cong (vec₁ ⊗ ι x) xs (i A.⊗ A.ι j)
    with (i ⟨ rev (pull-Vᵣ vec₁) ⟩) | Eq.inspect (i ⟨_⟩) (rev (pull-Vᵣ vec₁))
  ... | k ⊗ l | Eq.[ e ] rewrite sym (rev-fact (pull-Vᵣ vec₁) _ _ e) = refl
  map-vec₁≡map-ufft dft-cong vec@(vec₁ ⊗ (vec₂ ⊗ vec₃)) xs (i A.⊗ (i₁ A.⊗ i₂)) = 
        ufft-vec₁≡ufft dft-cong (vec₂ ⊗ vec₃) (nest xs i) (i₁ ⊗ i₂)

  ufft-vec₁≡ufft  _ (ι _) _ _ = refl
  ufft-vec₁≡ufft dft-cong (vec₁ ⊗ vec₂) xs (i₁ ⊗ i₂) =
    trans
      (map-vec₁≡map-ufft dft-cong (vec₁ ⊗ vec₂) _ (i₁ ⊗ i₂))
      (ufft-cong dft-cong _ _ (λ j → 
        cong₂
          _*ᶜ_
          refl
          (map-vec₁≡map-ufft dft-cong (vec₂ ⊗ vec₁) _ (j ⊗ i₁))
      ) i₂)

  mapVec₁-cong : {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
              {twid : ∀ {s p} → P s → P p → ℂ}
            → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                        → ∀ i → dft {n} a i ≡ dft b i)
            → ∀ {s p : S}
            → (v : VEC V (s ⊗ p))
            → ∀ a b → (∀ i → a i ≡ b i)
            → ∀ i → mapVec₁ dft (ufft-vec₁ dft twid) v a i ≡ mapVec₁ dft (ufft-vec₁ dft twid) v b i
  mapVec₁-cong dft-cong vec a b prf i@(i₁ ⊗ i₂) =
    map-vec₁≡map-ufft dft-cong vec _ i
    ⊡
    ufft-cong dft-cong _ _ (λ i → prf (i₁ ⊗ i)) i₂
    ⊡
    sym (map-vec₁≡map-ufft dft-cong vec _ i)

  -----------------------------------------------------------------------------

  map-vec₂≡map-vec₁ :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                    → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                    → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                                → ∀ i → dft {n} a i ≡ dft b i)
                    → ∀ (vec : VEC V (s ⊗ p))
                    → ∀ (xs : Ar (s ⊗ p) ℂ)
                    → ∀ (i : P (s ⊗ p)) 
                    → mapVec₁ dft (ufft-vec₂ dft twid) vec xs i ≡ mapVec₁ dft (ufft-vec₁ dft twid) vec xs i

  ufft-vec₂≡ufft-vec₁ :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                  → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                  → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                              → ∀ i → dft {n} a i ≡ dft b i)
                  → ∀ (vec : VEC V s)
                  → ∀ (xs : Ar s ℂ)
                  → ∀ (i : P s) 
                  →  ufft-vec₂ dft twid vec xs i
                     ≡ 
                     ufft-vec₁ dft twid vec xs i

  map-vec₂≡map-vec₁ dft-cong (vec₁ ⊗ ι x) xs (i₁ A.⊗ A.ι x₁) = refl
  map-vec₂≡map-vec₁ dft-cong (vec₁ ⊗ (vec₂ ⊗ vec₃)) xs (i₁ A.⊗ (i₂ A.⊗ i₃)) 
      = ufft-vec₂≡ufft-vec₁ dft-cong (vec₂ ⊗ vec₃) (nest xs i₁) (i₂ ⊗ i₃)

  ufft-vec₂≡ufft-vec₁ dft-cong (ι x) xs i = refl
  ufft-vec₂≡ufft-vec₁ {dft = dft} {twid = twid} dft-cong (vec₁ ⊗ vec₂) xs (i₁ ⊗ i₂) =
      (map-vec₂≡map-vec₁ dft-cong (vec₁ ⊗ vec₂) _ (i₁ ⊗ i₂))
      ⊡
      (mapVec₁-cong dft-cong (vec₁ ⊗ vec₂) _ 
        (reshape swap (zipWith _*ᶜ_ (unnest twid) (mapVec₁ dft (ufft-vec₂ dft twid) (vec₂ ⊗ vec₁) (reshape swap xs))))
        (λ{(j₁ ⊗ j₂) → mapTwid₂-prop twid (vec₂ ⊗ vec₁) (mapVec₁ dft (ufft-vec₂ dft twid) (vec₂ ⊗ vec₁) (reshape swap xs)) (j₂ ⊗ j₁) }) 
        (i₁ ⊗ i₂)
      )
      ⊡
      (mapVec₁-cong dft-cong (vec₁ ⊗ vec₂) _ _ (λ{(j₁ ⊗ j₂) → 
              cong₂
                _*ᶜ_
                refl
                (map-vec₂≡map-vec₁ dft-cong (vec₂ ⊗ vec₁) _ (j₂ ⊗ j₁)) 
      }) (i₁ ⊗ i₂))

  mapVec₂-cong : {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
              {twid : ∀ {s p} → P s → P p → ℂ}
            → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                        → ∀ i → dft {n} a i ≡ dft b i)
            → ∀ {s p : S}
            → (v : VEC V (s ⊗ p))
            → ∀ a b → (∀ i → a i ≡ b i)
            → ∀ i → mapVec₁ dft (ufft-vec₂ dft twid) v a i ≡ mapVec₁ dft (ufft-vec₂ dft twid) v b i
  mapVec₂-cong dft-cong vec _ _ prf i = 
    map-vec₂≡map-vec₁ dft-cong vec _ i
    ⊡
    mapVec₁-cong dft-cong vec _ _ prf i 
    ⊡
    sym (map-vec₂≡map-vec₁ dft-cong vec _ i)

  -----------------------------------------------------------------------------
  map-vec₃≡map-vec₂ :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                          → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                          → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                                      → ∀ i → dft {n} a i ≡ dft b i)
                          → (twiddle? : Bool)
                          → ∀ (vec : VEC V (s ⊗ p))
                          → ∀ (xs : Ar (s ⊗ p) ℂ)
                          → ∀ (i : P (s ⊗ p)) 
                          → mapVec₃ dft twid twiddle? vec xs i 
                          ≡ 
                            (if twiddle? then 
                              mapTwid₂ twid vec (mapVec₁ dft (ufft-vec₂ dft twid) vec xs) i
                            else
                              mapVec₁ dft (ufft-vec₂ dft twid) vec xs i
                            )

  map-vec₃≡map-vec₂ _ false (_ ⊗ ι _) _ (_ A.⊗ A.ι _) = refl
  map-vec₃≡map-vec₂ dft-cong false (vec₁ ⊗ (vec₂ ⊗ vec₃)) _ (i₁ A.⊗ (i₂ A.⊗ i₃)) 
      = map-vec₃≡map-vec₂ dft-cong false (vec₂ ⊗ vec₃) _ (i₂ ⊗ i₃)
      ⊡ mapVec₂-cong dft-cong (vec₂ ⊗ vec₃) _ _ (λ{(j₁ ⊗ j₂) → 
          map-vec₃≡map-vec₂ dft-cong true (vec₃ ⊗ vec₂) _ (j₂ ⊗ j₁)
        }) (i₂ ⊗ i₃)
  map-vec₃≡map-vec₂ dft-cong true (vec ⊗ ι _) xs (i ⊗ ι x) 
    with (((i ⟨ rev (pull-Vᵣ vec) ⟩) ⊗ ι x) ⟨ assocl ⟩) 
  ... | j₁ ⊗ j₂ rewrite rev-rev (assocr ∙ pull-Vᵣ vec ⊕ eq) (j₁ ⊗ j₂) = refl
  map-vec₃≡map-vec₂ dft-cong true (vec₁ ⊗ (vec₂ ⊗ vec₃)) xs (i₁ ⊗ (i₂ ⊗ i₃)) 
  -- TODO: Improve.... more.....
  --  with ((i₁ ⊗ (i₂ ⊗ i₃)) ⟨ (rev (assocr ∙ (pull-Vᵣ vec₁) ⊕ eq )) ⟩) 
  --     | (((i₁ ⊗ (i₂ ⊗ i₃)) ⟨ (rev (assocr ∙ (pull-Vᵣ vec₁) ⊕ eq )) ⟩) ⟨ assocr ∙ pull-Vᵣ vec₁ ⊕ eq ⟩)
  --... | j₁ ⊗ j₂ | j₃ ⊗ j₄ 
   with ((i₁ ⊗ (i₂ ⊗ i₃)) ⟨ (rev (assocr ∙ (pull-Vᵣ vec₁) ⊕ eq )) ⟩)  
  ... | j₁ ⊗ j₂ with ((j₁ ⊗ j₂) ⟨ assocr ∙ pull-Vᵣ vec₁ ⊕ eq ⟩)
  ...           | j₃ ⊗ j₄
    = cong₂ _*ᶜ_ refl (
          (map-vec₃≡map-vec₂
            dft-cong 
            false
            (vec₂ ⊗ vec₃) 
            (λ z → mapVec₃ _ _ true (vec₃ ⊗ vec₂) (λ z₁ → xs (j₃ ⊗ (z₁ ⟨ swap ⟩))) (z ⟨ swap ⟩)) 
            j₄
          )
          ⊡ mapVec₂-cong dft-cong (vec₂ ⊗ vec₃) _ _ (λ{(k₁ ⊗ k₂) → 
              map-vec₃≡map-vec₂ dft-cong true (vec₃ ⊗ vec₂) _ (k₂ ⊗ k₁)
            }) j₄
          )

  ufft-vec₃≡ufft-vec₂ :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                  → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                  → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                              → ∀ i → dft {n} a i ≡ dft b i)
                  → ∀ (vec : VEC V s)
                  → ∀ (xs : Ar s ℂ)
                  → ∀ (i : P s) 
                  →  ufft-vec₃ dft twid vec xs i
                     ≡ 
                     ufft-vec₂ dft twid vec xs i
  ufft-vec₃≡ufft-vec₂ dft-cong vec xs (A.ι x) = refl
  ufft-vec₃≡ufft-vec₂ dft-cong vec@(vec₁ ⊗ vec₂) xs (i₁ A.⊗ i₂) =
    map-vec₃≡map-vec₂ dft-cong false vec _ (i₁ ⊗ i₂)
    ⊡
    mapVec₂-cong dft-cong vec _ _ (λ{ (j₁ ⊗ j₂) → 
      map-vec₃≡map-vec₂ dft-cong true (vec₂ ⊗ vec₁) (reshape swap xs) (j₂ ⊗ j₁)
    }) (i₁ ⊗ i₂)


module MM (M₁ : Mon) where
  private
    variable
      X Y : Set
    S₁ = A.S M₁
    P₁ = A.P M₁

  mk-M₂ : Mon
  mk-M₂ = record {
      U    = S₁
    ; El   = P₁
    --; ι    = A.ι   (Mon.ι M₁)
    --; _⊗_  = ?
    --; unit-law  = ?
    --; pair-law  = ?
    --; flat = ?
    --; comm = ?
    }
    

module T (M₁ : Mon) where
  open Mon M₁ using (U; El)
  --open A M₁

  private variable
    X Y : Set

  S₁ = A.S M₁
  P₁ = A.P M₁
  Ar₁ = A.Ar M₁

  M₂ : Mon
  M₂ = record {
      U    = S₁
    ; El   = P₁
    }

  S₂  = A.S  M₂
  P₂  = A.P  M₂
  Ar₂ = A.Ar M₂

  flat-shp : S₂ → S₁
  flat-shp (A.ι x) = x
  flat-shp (s A.⊗ p) = flat-shp s A.⊗ flat-shp p

  flat-pos : ∀ {s} → P₂ s → P₁ (flat-shp s)
  flat-pos (A.ι i) = i
  flat-pos (i A.⊗ j) = flat-pos i A.⊗ flat-pos j

  flat-pos' : ∀ {s} → P₁ (flat-shp s) → P₂ s
  flat-pos' {A.ι x} i = A.ι i
  flat-pos' {s A.⊗ s₁} (i A.⊗ i₁) = flat-pos' i A.⊗ flat-pos' i₁

  flat-ar : ∀ {s} → Ar₂ s X → Ar₁ (flat-shp s) X
  flat-ar a i = a (flat-pos' i)

  flat-ar' : ∀ {s} → Ar₁ (flat-shp s) X → Ar₂ s X
  flat-ar' a i = a (flat-pos i)

  lift-ar : ∀ {s} → Ar₁ s X → Ar₂ (A.ι s) X
  lift-ar a (A.ι i) = a i

  flat-pos-pos' : ∀ {s} i → flat-pos {s} (flat-pos' i) ≡ i
  flat-pos-pos' {A.ι x} i = refl
  flat-pos-pos' {s A.⊗ p} (i A.⊗ i₁) 
    = cong₂ A._⊗_ (flat-pos-pos' {s} i) (flat-pos-pos' {p} i₁)


  dft₁ : ∀ {n} → Ar₁ (A.ι n) ℂ → Ar₁ (A.ι n) ℂ
  twid₁ : ∀ {s p} → P₁ s → P₁ p → ℂ
  dft₁-cong : ∀ {n} a b → (∀ i → a i ≡ b i)
          → ∀ i → dft₁ {n} a i ≡ dft₁ b i

  module F₁ = F M₁

  ufft₁ : ∀ {s} → _ → _
  ufft₁ {s} = F₁.ufft {s} dft₁ twid₁

  fft₁ : ∀ {s} → _ → _
  fft₁ {s} = F₁.fft {s} dft₁ twid₁
  
  ufft₁-cong : ∀ {s} a b → (∀ i → a i ≡ b i)
             → ∀ i → ufft₁ {s} a i ≡ ufft₁ b i
  ufft₁-cong {s} a b pf = F₁.ufft-cong dft₁-cong a b pf 
  
  dft₂ : ∀ {n} → Ar₂ (A.ι n) ℂ → Ar₂ (A.ι n) ℂ
  dft₂ a = lift-ar (ufft₁ (flat-ar a))

  twid₂ : ∀ {s p} → P₂ s → P₂ p → ℂ
  twid₂ i j = twid₁ (flat-pos i) (flat-pos j)

  module F₂ = F M₂

  ufft₂ : ∀ {s} → _ → _
  ufft₂ {s} = F₂.ufft {s} dft₂ twid₂

  fft₂ : ∀ {s} → _ → _
  fft₂ {s} = F₂.fft {s} dft₂ twid₂
  
  thm : ∀ {s} (a : Ar₂ s ℂ) 
      → ∀ i → flat-ar (ufft₂ a) i ≡ (ufft₁ (flat-ar a)) i
  thm {A.ι n} a (A.ι x) = refl
  thm {A.ι n} a (i A.⊗ i₁) = refl
  thm {s A.⊗ p} a (i A.⊗ j) 
      rewrite thm (λ j₁ →
               twid₁ (flat-pos j₁) (flat-pos {s} (flat-pos' i)) *ᶜ
               F.ufft M₂ --(A.S M₁) (A.P M₁)
               (λ a₁ → lift-ar (F₁.ufft dft₁ twid₁ (λ i₁ → a₁ (A.ι i₁))))
               (λ i₁ j₂ → twid₁ (flat-pos i₁) (flat-pos j₂))
               (λ j₂ → a (j₂ A.⊗ j₁)) (flat-pos' i)) j
      = ufft₁-cong _ _ (λ k → cong₂ _*ᶜ_ 
                     (cong₂ twid₁ (flat-pos-pos' {p} k)
                                  (flat-pos-pos' {s} i))
                     (thm (λ j₂ → a (j₂ A.⊗ flat-pos' k)) i)) j

module B where
  
  import Matrix as M
  import Matrix.Equality as ME
  open import Matrix.NonZero
  import Data.Fin as Fin
  open import Function.Bundles
  open Inverse

  inv₁ : {x : ⊤} → tt ≡ x
  inv₁ {tt} = refl

  inv₂ : {x : Fin 1} → Fin.zero ≡ x
  inv₂ {zero} = refl

  ℕ-Mon : Mon
  ℕ-Mon = record {
      U    = ℕ
    ; El   = Fin ∘ suc
    -- This being 0 feels wrong, as it should be an identity element and zero 
    -- is not identity for multiplication, but I believe the suc above fixes 
    -- this issue?
    --; ι    = 0
    --; _⊗_  = _*_
    --; unit-law  = record 
    --              { to        = λ _ → tt
    --              ; from      = λ _ → Fin.zero
    --              ; to-cong   = λ _ → refl
    --              ; from-cong = λ _ → refl
    --              ; inverse   = (λ _ → inv₁) , (λ _ → inv₂)
    --              }
    --; pair-law  = λ a b → record 
    --              { to        = ?
    --              ; from      = ?
    --              ; to-cong   = ?
    --              ; from-cong = ?
    --              ; inverse   = ?
    --              }
    --; flat = ?
    --; comm = ?
    }

  S₁ = A.S ℕ-Mon
  P₁ = A.P ℕ-Mon
  Ar₁ = A.Ar ℕ-Mon

  S₂ = Σ M.Shape (λ s₂ → NonZeroₛ s₂)
  P₂ = M.Position
  Ar₂ = M.Ar

  variable
    X : Set
    s₁ p₁ : S₁
    s₂ p₂ : S₂
    i₁ j₁ : P₁ s₁
    i₂ j₂ : P₂ (proj₁ s₂)
    xs : Ar₁ s₁ X
    ys : Ar₂ (proj₁ s₂) X

  --S₁-from-S₂ : Σ S₂ (λ s₂ → NonZeroₛ s₂) → S₁
  S₁-from-S₂ : S₂ → S₁
  S₁-from-S₂ (M.ι x , nz) = A.ι (Nat.pred x)
  S₁-from-S₂ ((s₂ M.⊗ p₂) , (nz₁ ⊗ nz₂)) = (S₁-from-S₂ (s₂ , nz₁)) A.⊗ (S₁-from-S₂ (p₂ , nz₂))

  S₁-to-S₂ : S₁ → S₂
  S₁-to-S₂ (A.ι x) = M.ι (suc x) , ι (record { nonZero = tt })
  S₁-to-S₂ (s₂ A.⊗ p₂) = let
                          MS₂ , nzS₂ = S₁-to-S₂ s₂
                          MP₂ , nzP₂ = S₁-to-S₂ p₂
                         in MS₂ M.⊗ MP₂ , nzS₂ ⊗ nzP₂


  -- Σ-≡-intro is taken from https://stackoverflow.com/a/37492419 , András Kovács under CC BY-SA 3.0
  Σ-≡-intro :
    ∀ {α β}{A : Set α}{B : A → Set β}{a a' : A}{b : B a}{b' : B a'}
    → (Σ (a ≡ a') λ p → subst B p b ≡ b') → (a , b) ≡ (a' , b')
  Σ-≡-intro (refl , refl) = refl

  S₂≡S₂-helper : proj₁ s₂ ≡ proj₁ p₂ → s₂ ≡ p₂
  S₂≡S₂-helper {_ , nzₗ} {._ , nzᵣ} refl = Σ-≡-intro (refl , nzₛ≡nzₛ nzₗ nzᵣ)

  S-inv₁ : S₁-to-S₂ (S₁-from-S₂ s₂) ≡ s₂
  S-inv₁ {M.ι (suc x) , ι record { nonZero = tt }} rewrite suc-pred (suc x) ⦃ record { nonZero = tt } ⦄ = refl
  S-inv₁ {(s₂ M.⊗ p₂) , (nzs ⊗ nzp)} = let 
                                        s₂-inv = S-inv₁ {s₂ , nzs}
                                        p₂-inv = S-inv₁ {p₂ , nzp}
                                      in S₂≡S₂-helper (cong₂ M._⊗_ (cong proj₁ s₂-inv) (cong proj₁ p₂-inv)) 

  S-inv₂ : S₁-from-S₂ (S₁-to-S₂ s₁) ≡ s₁
  S-inv₂ {A.ι x} = refl
  S-inv₂ {s₁ A.⊗ s₂} = cong₂ A._⊗_ S-inv₂ S-inv₂

  S₁↔S₂ : S₁ ↔ S₂
  to S₁↔S₂ = S₁-to-S₂
  from S₁↔S₂ = S₁-from-S₂
  to-cong S₁↔S₂ refl = refl
  from-cong S₁↔S₂ refl = refl
  proj₁ (inverse S₁↔S₂) refl = S-inv₁
  proj₂ (inverse S₁↔S₂) refl = S-inv₂

  P₁-to-P₂ : P₁ s₁ → P₂ (proj₁ $ S₁-to-S₂ s₁)
  P₁-to-P₂ (A.ι x) = M.ι x
  P₁-to-P₂ (i₁ A.⊗ j₁) = P₁-to-P₂ i₁ M.⊗ P₁-to-P₂ j₁

  P₁-from-P₂ : P₂ (proj₁ $ S₁-to-S₂ s₁) → P₁ s₁
  P₁-from-P₂ {A.ι _} (M.ι x) = A.ι x
  P₁-from-P₂ {_ A.⊗ _} (i₂ M.⊗ j₂) = P₁-from-P₂ i₂ A.⊗ P₁-from-P₂ j₂

  P-inv₁ : P₁-to-P₂ (P₁-from-P₂ i₂) ≡ i₂
  P-inv₁ {A.ι _} {M.ι _} = refl
  P-inv₁ {s₁ A.⊗ p₁} {i₂ M.⊗ j₂} {nz-s₁ ⊗ nz-p₁} = cong₂ M._⊗_ (P-inv₁ {s₁} {i₂} {nz-s₁}) (P-inv₁ {p₁} {j₂} {nz-p₁})

  P-inv₂ : P₁-from-P₂ (P₁-to-P₂ i₁) ≡ i₁
  P-inv₂ {A.ι _} {A.ι _} = refl
  P-inv₂ {_ A.⊗ _} {_ A.⊗ _} = cong₂ A._⊗_ P-inv₂ P-inv₂

  P₁↔P₂ : P₁ s₁ ↔ P₂ (proj₁ $ S₁-to-S₂ s₁)
  to P₁↔P₂ = P₁-to-P₂
  from P₁↔P₂ = P₁-from-P₂
  to-cong P₁↔P₂ refl = refl
  from-cong P₁↔P₂ refl = refl
  proj₁ (inverse (P₁↔P₂ {s₁})) {i₁} refl = P-inv₁ {s₁} {i₁} {proj₂ $ S₁-to-S₂ s₁}
  proj₂ (inverse P₁↔P₂) refl = P-inv₂

  Ar₁-from-Ar₂ : Ar₂ (proj₁ $ S₁-to-S₂ s₁) X → Ar₁ s₁ X
  Ar₁-from-Ar₂ ys i₁ = ys (P₁-to-P₂ i₁)

  Ar₁-to-Ar₂   : Ar₁ s₁ X → Ar₂ (proj₁ $ S₁-to-S₂ s₁) X
  Ar₁-to-Ar₂ xs i₂ = xs (P₁-from-P₂ i₂)

  ---- Well here to create a "Proper" isomorphism (or more, and isomorphism using
  ---- Function.Bundles) I would need extensionality to compare the elements of 
  ---- the array
  --Ar-inv₁ : Ar₁-to-Ar₂ (Ar₁-from-Ar₂ ys) ≡ ys
  --Ar-inv₁ {X} {s₁} {ys} = ?

  Ar-inv₁′ : ∀ (i₂ : P₂ (proj₁ $ S₁-to-S₂ s₁)) → Ar₁-to-Ar₂ {s₁} (Ar₁-from-Ar₂ ys) i₂ ≡ ys i₂
  Ar-inv₁′ {s₁} {X} {ys} {nz} i₂ = cong ys (P-inv₁ {s₁} {i₂} {nz})

  --Ar-inv₂ : Ar₁-from-Ar₂ (Ar₁-to-Ar₂ xs) ≡ xs
  --Ar-inv₂ {X} {s₁} {xs} = ?

  Ar-inv₂′ : ∀ (i : P₁ s₁) → Ar₁-from-Ar₂ (Ar₁-to-Ar₂ xs) i ≡ xs i
  Ar-inv₂′ {X} {s₁} {xs} i = cong xs P-inv₂

  --Ar₁↔Ar₂ : _↔_ (Ar₁ s₁ X) (Ar₂ (S₁-to-S₂ s₁) X)
  --to        Ar₁↔Ar₂ = Ar₁-to-Ar₂
  --from      Ar₁↔Ar₂ = Ar₁-from-Ar₂
  --to-cong Ar₁↔Ar₂ refl = refl
  --from-cong Ar₁↔Ar₂ refl = refl
  --proj₁ (inverse Ar₁↔Ar₂) refl = Ar-inv₁
  --proj₂ (inverse Ar₁↔Ar₂) refl = Ar-inv₂


    
module P where
  
  open import FFT cplx as OLDFFT
  import Proof cplx as Pr
  import Matrix as M
  import Matrix.Reshape as R
  import Matrix.NonZero as NZ

  open import Relation.Nullary
  open import Data.Empty

  open Cplx cplx using (+-*-isCommutativeRing)
  open import Algebra.Structures as AlgebraStructures
  open AlgebraStructures {A = ℂ} _≡_
  open AlgebraStructures.IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid) renaming (*-comm to *𝕔-comm)

  open B
  module NEWFFT = F ℕ-Mon
  module A′ = A ℕ-Mon  

  FFT′-cong : ∀ (xs ys : Ar₂ (proj₁ s₂) ℂ) 
              → (∀ j → xs j ≡ ys j) 
              → (∀ i → FFT′ {{ proj₂ s₂ }} xs i ≡ FFT′ {{ proj₂ s₂ }} ys i)
  FFT′-cong {_ , nz-s} _ _ = Pr.FFT′-cong ⦃ nz-s ⦄

  newTwid : ∀ {s p : A′.S} → A′.P s → A′.P p → ℂ
  newTwid {s} {p} i j = OLDFFT.twiddles 
                          {{ proj₂ (S₁-to-S₂ s) NZ.⊗ proj₂ (S₁-to-S₂ p) }} 
                          ((P₁-to-P₂ i) M.⊗ (P₁-to-P₂ j))

  Rtrans≡Atrans : (R.recursive-transpose $ proj₁ (S₁-to-S₂ s₁)) ≡ proj₁ (S₁-to-S₂ (A′.transp s₁))
  Rtrans≡Atrans {A.ι _} = refl
  Rtrans≡Atrans {s₁ A.⊗ s₂} = cong₂ M._⊗_ (Rtrans≡Atrans {s₂}) (Rtrans≡Atrans {s₁})

  lemma₂ : M.length (R.recursive-transpose (proj₁ (S₁-to-S₂ s₁))) ≡
           M.length (proj₁ (S₁-to-S₂ (A′.transp s₁)))
  lemma₂ {A.ι x} = refl
  lemma₂ {s₁ A.⊗ s₂} = cong₂ _*_ (lemma₂ {s₂}) (lemma₂ {s₁})

  lemma₁ : iota 
            ((P₁-to-P₂ i₁ R.⟨ R.rev R.recursive-transposeᵣ ⟩) R.⟨ R.rev R.♭ ⟩) 
            ≡ 
           iota 
            (P₁-to-P₂ (i₁ A′.⟨ A′.transpᵣ ⟩) R.⟨ R.rev R.♭ ⟩)
  lemma₁ {A.ι _} {A.ι _} = refl
  lemma₁ {s₁ A.⊗ s₂} {i₁ A.⊗ i₂} =
      Pr.iota-split 
              {R.recursive-transpose $ proj₁ $ S₁-to-S₂ s₁} 
              {R.recursive-transpose $ proj₁ $ S₁-to-S₂ s₂} 
              ((P₁-to-P₂ i₁ R.⟨ R.rev R.recursive-transposeᵣ ⟩) R.⟨ R.rev R.♭ ⟩)
              ((P₁-to-P₂ i₂ R.⟨ R.rev R.recursive-transposeᵣ ⟩) R.⟨ R.rev R.♭ ⟩)
      ⊡ cong₂ Nat._+_ 
                {   M.length (R.recursive-transpose (proj₁ (S₁-to-S₂ s₁))) 
                  * 
                    iota ((P₁-to-P₂ i₂ R.⟨ R.rev R.recursive-transposeᵣ ⟩) R.⟨ R.rev R.♭ ⟩)
                } 
                {M.length (proj₁ (S₁-to-S₂ (A′.transp s₁))) * iota (P₁-to-P₂ (i₂ A′.⟨ A′.transpᵣ ⟩) R.⟨ R.rev R.♭ ⟩)} 
                (cong₂ 
                    _*_ 
                    {M.length (R.recursive-transpose (proj₁ (S₁-to-S₂ s₁)))}
                    {M.length (proj₁ (S₁-to-S₂ (A′.transp s₁)))}
                    (lemma₂ {s₁})
                    (lemma₁ {_} {i₂})
                ) 
                (lemma₁ {_} {i₁})
      ⊡ (sym (Pr.iota-split 
              {proj₁ $ S₁-to-S₂ (A′.transp s₁)} 
              {proj₁ $ S₁-to-S₂ (A′.transp s₂)}
              (P₁-to-P₂ (i₁ A′.⟨ A′.transpᵣ ⟩) R.⟨ R.rev R.♭ ⟩)
              (P₁-to-P₂ (i₂ A′.⟨ A′.transpᵣ ⟩) R.⟨ R.rev R.♭ ⟩)
      ))

  prf : ∀ (xs : Ar₁ s₁ ℂ) (i : P₁ (s₁)) → 
        OLDFFT.FFT′ 
          {{ proj₂ $ S₁-to-S₂ s₁ }}
          (Ar₁-to-Ar₂ xs) 
          (R._⟨_⟩ (P₁-to-P₂ i) (R.rev R.recursive-transposeᵣ))
      ≡ NEWFFT.fft 
          (Ar₁-from-Ar₂ ∘ OLDFFT.DFT ∘ Ar₁-to-Ar₂) 
          newTwid
          xs 
          (A′._⟨_⟩ i A′.transpᵣ)
  prf {A.ι _} _ (A.ι _) = refl
  prf {s₁ A.⊗ s₂} xs (i₁ A.⊗ i₂) with NZ.nonZeroDec (proj₁ (S₁-to-S₂ s₁) M.⊗ proj₁ (S₁-to-S₂ s₂))
  ... | no ¬a = ⊥-elim (¬a $ proj₂ (S₁-to-S₂ s₁) NZ.⊗ proj₂ (S₁-to-S₂ s₂))
  ... | yes (nz-s₁ NZ.⊗ nz-s₂) =
    trans 
      (FFT′-cong 
          _
          _ 
          (λ j → 
            trans 
              (*𝕔-comm _ _) 
              (cong₂ _*ᶜ_ 
                  (Pr.-ω-cong₂ 
                    {{ NZ.nonZeroₛ-s⇒nonZero-s (nz-s₂ NZ.⊗ (NZ.nonZeroₛ-s⇒nonZeroₛ-sᵗ nz-s₁)) }} 
                    {{ NZ.nonZeroₛ-s⇒nonZero-s (nz-s₂ NZ.⊗ (proj₂ $ S₁-to-S₂ (A′.transp s₁))) }} 
                    (cong₂ _*_ 
                        {M.length (proj₁ (S₁-to-S₂ s₂))} 
                        {M.length (proj₁ (S₁-to-S₂ s₂))} 
                        {M.length (R.recursive-transpose $ proj₁ (S₁-to-S₂ s₁))} 
                        {M.length (proj₁ (S₁-to-S₂ (A′.transp s₁)))} 
                        refl 
                        (cong M.length (Rtrans≡Atrans {s₁}))
                    )
                    (cong₂ _*_ 
                        (cong 
                            iota 
                            (cong 
                                (λ f → R._⟨_⟩ f (R.rev R.♭)) 
                                (sym (P-inv₁ {s₂} {j} {nz-s₂}))
                            )
                        )
                        (lemma₁ {s₁} {i₁})
                    )
                  )
                  (prf (λ j₁ → _) i₁)
              )
          ) 
          (P₁-to-P₂ i₂ R.⟨ R.rev R.recursive-transposeᵣ ⟩)
      )
      (prf {s₂} 
          (λ j →
              newTwid {s₂} {A′.transp s₁} j (i₁ A′.⟨ A′.transpᵣ ⟩)
             *ᶜ
             NEWFFT.fft
              (Ar₁-from-Ar₂ ∘ OLDFFT.DFT ∘ Ar₁-to-Ar₂)
              newTwid
              (λ j₁ → xs (j₁ A′.⊗ j)) (i₁ A′.⟨ A′.transpᵣ ⟩)
          ) i₂)


record Change-Major (M : Mon) : Set where
  open A M
  open Mon M using (U; El)
  field
    change-major : ∀ {s : S} → Reshape (transp s) s

    change-major-transp : ∀ { s } → ∀ i → i ⟨ change-major {s} ∙ (rev transpᵣ) ⟩ ≡ i ⟨ transpᵣ ∙ (rev change-major) ⟩
    change-major-rev  : ∀ {s : S} → ∀ i → i ⟨ rev (change-major {s}) ∙ change-major ⟩  ≡ i ⟨ eq ⟩ 
    change-major-id : ∀ {u : U} {x : El u} → (ι x) ⟨ change-major ⟩ ≡ ι x
    

record dft-fft (M : Mon) (CM : Change-Major M) : Set₁ where
  module FM = F M
  open A M
  open Change-Major CM
  open Mon M using (U)

  field
    dft      : ∀ {n : U} → Ar (ι n) ℂ → Ar (ι n) ℂ
    dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) → ∀ i → dft {n} a i ≡ dft b i

    twiddles : ∀ {s p : S} → P s → P p → ℂ
    transp-twid : ∀ {s p} → ∀ {i j} → twiddles ((i ⟨ transpᵣ ⟩) ⟨ transpᵣ ⟩) j ≡ twiddles {s} {p} i j


    size : S → U

    flatten : ∀ {s : S} → Reshape s (ι (size s))

    prf :   ∀ {s : S}
          → ∀ (xs : Ar s ℂ)
          → ∀ (i : P s) 
          → reshape (rev flatten) (dft (reshape flatten xs)) i
            ≡ 
            reshape change-major (FM.fft dft twiddles xs) i

module L (M₁ : Mon) (CM₁ : Change-Major M₁) (rel : dft-fft M₁ CM₁) (CM₂ : Change-Major (MM.mk-M₂ M₁)) where
  open Change-Major CM₁
  open Change-Major CM₂ using () renaming (change-major to change-major₂; change-major-id to change-major-id₂)
  
  variable
    X Y : Set

  M₂ = MM.mk-M₂ M₁

  open Mon M₁ using (U₁; El₁)
  open Mon M₂ using (U₂; El₂)

  module FM₁ = F M₁
  module FM₂ = F M₂

  open A M₂ using () renaming
    ( S to S₂
    ; P to P₂ 
    ; Ar to Ar₂
    ; ι to ι₂
    ; _⊗_ to _⊗₂_
    ; unnest to unnest₂
    ; nest to nest₂
    ; imap to imap₂
    ; zipWith to zipWith₂
    ; reshape to reshape₂
    ; Reshape to Reshape₂
    ; swap to swap₂
    ; rev to rev₂
    ; map to map₂
    ; _⟨_⟩ to _⟨_⟩₂
    ; transpᵣ to transpᵣ₂
    ; transp to transp₂
    ; eq to eq₂
    ; _⊕_ to _⊕₂_
    ; rev-rev′ to rev-rev′₂
    ; rev-rev to rev-rev₂
    )

  open A M₁ using () renaming
    ( S to S₁
    ; P to P₁ 
    ; Ar to Ar₁
    ; ι to ι₁
    ; _⊗_ to _⊗₁_
    ; unnest to unnest₁
    ; nest to nest₁
    ; imap to imap₁
    ; zipWith to zipWith₁
    ; reshape to reshape₁
    ; Reshape to Reshape₁
    ; swap to swap₁
    ; rev to rev₁
    ; map to map₁
    ; _⟨_⟩ to _⟨_⟩₁
    ; transpᵣ to transpᵣ₁
    ; _∙_ to _∙₁_
    ; transp to transp₁
    ; eq to eq₁
    ; _⊕_ to _⊕₁_
    ; rev-rev′ to rev-rev′₁
    ; rev-rev to rev-rev₁
    )

  lower-shp : S₂ → S₁
  lower-shp (A.ι x) = x
  lower-shp (s₁ ⊗₂ s₂) = lower-shp s₁ ⊗₁ lower-shp s₂
  
  shp-map : S₂ → (S₁ → S₁) → S₂
  shp-map (A.ι x) f = A.ι (f x)
  shp-map (s₁ A.⊗ s₂) f = (shp-map s₁ f) A.⊗ (shp-map s₂ f)

  lower-P : ∀ {s : S₂} → P₂ s → P₁ (lower-shp s) 
  lower-P (A.ι x) = x
  lower-P (p₁ A.⊗ p₂) = lower-P p₁ ⊗₁ lower-P p₂ 

  raise-P : ∀ {s : S₂} → P₁ (lower-shp s) → P₂ s
  raise-P {A.ι x} i = ι₂ i
  raise-P {s₁ A.⊗ s₂} (i₁ A.⊗ i₂) = (raise-P i₁) ⊗₂ (raise-P i₂)
  
  raise-lower-P : 
                  ∀ {s} 
                → ∀ (i : P₁ (lower-shp s)) 
                → lower-P {s} (raise-P i) ≡ i
  raise-lower-P {A.ι x} i = refl
  raise-lower-P {s₁ A.⊗ s₂} (i₁ A.⊗ i₂) rewrite
      raise-lower-P {s₁} i₁
    | raise-lower-P {s₂} i₂ = refl

  {-
  resh-map : ∀ {s : S₂} → P₂ s → {f : S₁ → S₁} → (∀ {s₁ : S₁} → P₁ s₁ → P₁ (f s₁)) → P₂ (shp-map s f)
  resh-map (A.ι x)     g = A.ι (g x)
  resh-map (i₁ A.⊗ i₂) g = (resh-map i₁ g) A.⊗ (resh-map i₂ g)
  -}

  resh-map : ∀ {s : S₂} → P₂ s → {f : S₁ → S₁} → (∀ {s₁ : S₁} → Reshape₁ (f s₁) s₁) → P₂ (shp-map s f)
  resh-map (A.ι x)     r = A.ι (x ⟨ r ⟩₁)
  resh-map (i₁ A.⊗ i₂) r = (resh-map i₁ r) A.⊗ (resh-map i₂ r)

  lower-P-raise-P-inv : ∀ {s : S₂} → ∀ {p : P₁ (lower-shp s)} → (lower-P {s} (raise-P p)) ≡ p
  lower-P-raise-P-inv {A.ι x} {p} = refl
  lower-P-raise-P-inv {s₁ A.⊗ s₂} {p₁ A.⊗ p₂} rewrite
      lower-P-raise-P-inv {s₁} {p₁}
    | lower-P-raise-P-inv {s₂} {p₂}
    = refl
  
  lower-Ar : ∀ {s : S₂} → Ar₂ s X → Ar₁ (lower-shp s) X
  lower-Ar {s = s} xs i = xs (raise-P i)

  raise-Ar : ∀ {s : S₂} → Ar₁ (lower-shp s) X → Ar₂ s X
  raise-Ar {s = s} xs i = xs (lower-P i)

  open dft-fft rel

  -- This performs a transposition on the outer shape at the end, and a 
  -- transposition on the inner shape at each outer leaf
  ufft-two-level : ∀ {s : S₂} 
                    → Ar₂ s ℂ → Ar₂ s ℂ
  ufft-two-level {ι₂ n} xs (ι₂ i) =
        reshape₁ 
            transpᵣ₁
            --change-major 
            (FM.pre-ufft 
              dft 
              (λ j₁ j₂ → twiddles (j₁ ⟨ transpᵣ₁ ⟩₁) j₂) 
              (reshape₁ (rev₁ transpᵣ₁) (lower-Ar xs))
            ) i
  ufft-two-level {s ⊗₂ p} a =
    let
      c = unnest₂ $ imap₂ 
          (λ i → 
            zipWith₂ 
              _*ᶜ_ 
              (λ j → twiddles
                  {lower-shp p} {transp₁ (lower-shp s)} (lower-P i) ((lower-P j) ⟨ transpᵣ₁ ⟩₁)
              )
            ∘ ufft-two-level {s} 
          )
        (nest₂ (reshape₂ swap₂ a))
      d = map₂ (ufft-two-level {p}) (nest₂ (reshape₂ swap₂ c))
    in (unnest₂ d)

  ufft-two-level≡ufft : ∀ {s : S₂}
                      → ∀ (xs : Ar₂ s ℂ)
                      → ∀ (ys : Ar₂ s ℂ)
                      → (∀ (i : P₂ s) → xs i ≡ ys i)
                      → ∀ (i : P₂ s)
                      → reshape₂ 
                          (rev₂ transpᵣ₂) 
                          (ufft-two-level xs) 
                          (i ⟨ transpᵣ₂ ⟩₂)
                      ≡
                        reshape₁ 
                          (rev₁ transpᵣ₁) 
                          (FM.ufft dft (λ i j → twiddles i (j ⟨ transpᵣ₁ ⟩₁)) (lower-Ar ys))
                          ((lower-P i) ⟨ transpᵣ₁ ⟩₁)
  ufft-two-level≡ufft {A.ι n} xs ys prf (A.ι x) =
      FM.pre-ufft≡post-ufft {_} {dft} {twiddles} transp-twid dft-cong (lower-Ar xs) (x ⟨ transpᵣ₁ ⟩₁) --(x ⟨ transpᵣ₁ ⟩₁)
      ⊡ FM.ufft-cong dft-cong _ _ (λ j → prf (A.ι j)) (x ⟨ transpᵣ₁ ∙₁ rev₁ transpᵣ₁ ⟩₁)
  ufft-two-level≡ufft {s₁ A.⊗ s₂} xs ys prf (i₁ A.⊗ i₂) =
      ufft-two-level≡ufft 
        _ 
        _
        (λ j₁ → 
          cong₂   
            _*ᶜ_
            refl
            (ufft-two-level≡ufft _ _ (λ j₂ → prf (j₂ ⊗₂ j₁)) i₁)
        ) 
        i₂
    ⊡ 
      FM.ufft-cong dft-cong 
        _ 
        _ 
        (λ j → 
          cong₂ _*ᶜ_ (
            cong₂
              twiddles 
              (raise-lower-P {s₂} j) 
              (cong _⟨ transpᵣ₁ ⟩₁ 
                ( (cong (lower-P {s₁}) {((i₁ ⟨ transpᵣ₂ ⟩₂) ⟨ rev₂ transpᵣ₂ ⟩₂)} {i₁} (rev-rev₂ transpᵣ₂ i₁))
                ⊡ (sym (rev-rev₁ transpᵣ₁ (lower-P i₁)))
              ))
          ) refl
        ) 
        ((lower-P i₂ ⟨ transpᵣ₁ ⟩₁) ⟨ rev₁ transpᵣ₁ ⟩₁)

  

  {-
  ufft-two-level₃ : ∀ {s : S₂} 
                    → (twid : ∀ {s p} → P₁ s → P₁ p → ℂ)
                    → Ar₂ s ℂ → Ar₂ s ℂ
  ufft-two-level₃ {ι₂ n} twid xs (ι₂ i) =
        -- Change major feels more correct here, but transpᵣ₁ actually works...
        reshape₁ transpᵣ₁ (FM.pre-ufft dft twid (reshape₁ (rev₁ transpᵣ₁) (lower-Ar xs))) i
        --reshape₁ change-major (FM.pre-ufft dft twid (reshape₁ (rev₁ transpᵣ₁) (lower-Ar xs))) i
  ufft-two-level₃ {s ⊗₂ p} twid a =
    let 
      c = unnest₂ $ imap₂ 
          (λ i → 
            zipWith₂ 
              _*ᶜ_ 
              (λ j → twid 
                  --{(lower-shp (shp-map s transp₁))} 
                  --{(lower-shp (shp-map p transp₁))} 
                  ((lower-P (resh-map i transpᵣ₁)))
                  ((lower-P (resh-map j transpᵣ₁)))
              )
            ∘ ufft-two-level₃ {p} twid
          )
        (nest₂ a)
      d = map₂ (ufft-two-level₃ {s} twid) (nest₂ (reshape₂ swap₂ c))
    in reshape₂ swap₂ (unnest₂ d)

  lemma₁ : ∀ {s} 
         → ∀ (i : P₂ s) 
         → lower-P (resh-map (i ⟨ transpᵣ₂ ⟩₂) transpᵣ₁) 
          ≡ 
           ? --(lower-P i) ⟨ transpᵣ₁ ⟩₁

  -- I Think this version is the nicest, but I belive the relation between xs 
  -- and ys is wrong
  ufft-two-level-transp₃ : ∀ {s : S₂}
                        → (twid : ∀ {s p} → P₁ s → P₁ p → ℂ)
                        → ∀ (xs : Ar₂ (transp₂ s) ℂ)
                        → ∀ (ys : Ar₁ (transp₁ (lower-shp s)) ℂ)
                        → (∀ (i : P₂ s) → xs (i ⟨ transpᵣ₂ ⟩₂) ≡ ys ((lower-P i) ⟨ transpᵣ₁ ⟩₁))
                        → ∀ (i : P₂ s)
                        → (ufft-two-level₃ twid xs) (i ⟨ transpᵣ₂ ⟩₂)
                        ≡ 
                          (FM.pre-ufft dft twid ys) ((lower-P i) ⟨ transpᵣ₁ ⟩₁)
  ufft-two-level-transp₃ {A.ι n} twid xs ys prf (A.ι x) =
      FM.pre-ufft-cong dft-cong _ _ 
        (λ i → prf (A.ι (i ⟨ rev₁ transpᵣ₁ ⟩₁)) ⊡ (cong ys (rev-rev′₁ transpᵣ₁ _))) (x ⟨ transpᵣ₁ ⟩₁)
  ufft-two-level-transp₃ {s A.⊗ s₁} twid xs ys prf (i₁ A.⊗ i₂) =
      ufft-two-level-transp₃ twid _ _ 
        (λ j₁ → 
          cong₂
            _*ᶜ_
            ? --(cong₂ twid ? ?)
            (ufft-two-level-transp₃ twid _ _ 
              (λ j₂ → 
                prf (j₂ A.⊗ j₁)
              ) 
              i₁
            )
        ) i₂
      
  {-
  ufft-two-level-transp : ∀ {s : S₂}
                        → ∀ (xs : Ar₂ s ℂ)
                        → ∀ (i : P₂ s)
                        → (reshape₂ 
                                change-major₂ 
                                (ufft-two-level₃ (λ i j → twiddles (i ⟨ transpᵣ₁ ⟩₁) j) (reshape₂ (rev₂ transpᵣ₂) xs))
                          ) i
                        ≡ 
                          reshape₁ (rev₁ flatten) (dft (reshape₁ flatten (lower-Ar xs))) (lower-P i)
  ufft-two-level-transp {A.ι n} xs (A.ι x) rewrite change-major-id₂ {n} {x} = 
      (FM₁.pre-ufft≡fft {_} {dft} {twiddles} transp-twid dft-cong (lower-Ar xs) (x ⟨ change-major ⟩₁))
    ⊡
      sym (prf (lower-Ar xs) x)
  ufft-two-level-transp {s₁ A.⊗ s₂} xs (i₁ A.⊗ i₂) with 
        ((lower-P (i₁ A.⊗ i₂)))  
      | ((i₁ A.⊗ i₂) ⟨ change-major₂ ⟩₂ ⟨ swap₂ ⟩₂) --⟨ rev₂ change-major₂ ⊕₂ rev₂ change-major₂ ⟩₂)
  ... | k₁ A.⊗ k₂ | j₁ A.⊗ j₂ =
    begin
      --_ ≡⟨ ufft-two-level-transp _  ⟩
      _ ≡⟨ ? ⟩
      _ ∎
  -}

  ufft-two-level-transp₂ : 
      ∀ {s : S₂}
    → ∀ (twid : ∀ {s p} → P₁ s → P₁ p → ℂ)
    → ∀ (xs : Ar₂ s ℂ)
    → ∀ (i : P₂ s)
    → (ufft-two-level₃ twid (reshape₂ (rev₂ transpᵣ₂) xs)) (i ⟨ transpᵣ₂ ⟩₂)
    ≡ 
      (FM.pre-ufft dft twid (reshape₁ (rev₁ transpᵣ₁) (lower-Ar xs))) ((lower-P i) ⟨ transpᵣ₁ ⟩₁)
  ufft-two-level-transp₂ {A.ι n} twid xs (A.ι x) = refl
  ufft-two-level-transp₂ {s₁ A.⊗ s₂} twid xs (i₁ A.⊗ i₂) = ?


  --ufft-two-level-transp₁ : ∀ {s : S₂}
  --                      → ∀ (xs : Ar₂ (transp₂ s) ℂ)
  --                      → ∀ (ys : Ar₂ s ℂ)
  --                      → (∀ i → xs (i ⟨ transpᵣ₂ ⟩₂) ≡ ys i)
  --                      → ∀ (i : P₂ s)
  --                      → (reshape₂ 
  --                              change-major₂ 
  --                              (ufft-two-level₃ (λ i j → twiddles (i ⟨ transpᵣ₁ ⟩₁) j) xs)
  --                        ) i
  --                      ≡ 
  --                        reshape₁ (rev₁ flatten) (dft (reshape₁ flatten (lower-Ar ys))) (lower-P i)
  --ufft-two-level-transp₁ {A.ι n} xs ys prf (A.ι x) rewrite change-major-id₂ {n} {x} =
  --    (FM₁.pre-ufft≡fft {_} {dft} {twiddles} transp-twid dft-cong (lower-Ar xs) (x ⟨ change-major ⟩₁))
  --    ⊡ 
  --    sym (prf (lower-Ar xs) x)
  --ufft-two-level-transp₁ {s A.⊗ s₁} xs ys prf (i A.⊗ i₁) = ?
-}
