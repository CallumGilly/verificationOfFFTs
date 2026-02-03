open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Fin as Fin
open import Data.Bool
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong)
open Eq.≡-Reasoning
open import Function

open import Data.Unit
-- This gives a warn on older versions of Agda when Product doesnt have a zipWith method
open import Data.Product hiding (swap; map; zipWith)

open import Complex using (Cplx)

module _ (cplx : Cplx) where

open Cplx cplx using (ℂ) renaming (_*_ to _*ᶜ_)

--postulate
--  ℂ : Set
--  _*ᶜ_ : ℂ → ℂ → ℂ


record Mon : Set₁ where
  field
    U : Set
    El : U → Set

    ι : U
    _⊗_ : U → U → U

    unit-law : El ι ↔ ⊤
    pair-law : ∀ a b → El (a ⊗ b) ↔ El a × El b

    flat : ?

record Uops (U : Set) (El : U → Set) : Set where
  field
    sum : ∀ u → (El u → ℂ) → ℂ
    -ω : U → ℂ → ℂ

module A (U : Set) (El : U → Set) where
--module A (M : Mon) where
--  open Mon M using (U; El)

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

  _⟨_⟩ : P s → Reshape p s → P p
  i ⟨ eq ⟩ = i
  (i ⊗ i₁) ⟨ r ⊕ r₁ ⟩ = (i ⟨ r ⟩) ⊗ (i₁ ⟨ r₁ ⟩)
  i ⟨ r ∙ r₁ ⟩ = (i ⟨ r ⟩) ⟨ r₁ ⟩
  (i ⊗ i₁) ⟨ swap ⟩ = i₁ ⊗ i
  ((i ⊗ j) ⊗ k) ⟨ assocl ⟩ = i ⊗ (j ⊗ k)
  (i ⊗ (j ⊗ k)) ⟨ assocr ⟩ = (i ⊗ j) ⊗ k

  rev : Reshape s p → Reshape p s
  rev eq = eq
  rev (r₁ ⊕ r₂) = (rev r₁) ⊕ (rev r₂)
  rev (r₁ ∙ r₂) = (rev r₂) ∙ (rev r₁)
  rev swap = swap
  rev assocl = assocr
  rev assocr = assocl

  rev-rev : ∀ (r : Reshape s p) (i : P p) →  i ⟨ r ∙ rev r ⟩ ≡ i
  rev-rev eq i = refl
  rev-rev (r₁ ⊕ r₂) (i₁ ⊗ i₂) rewrite rev-rev r₁ i₁ | rev-rev r₂ i₂ = refl
  rev-rev (r₁ ∙ r₂) i rewrite rev-rev r₂ (i ⟨ r₁ ⟩) | rev-rev r₁ i  = refl
  rev-rev swap (i₁ ⊗ i₂) = refl
  rev-rev assocl (i₁ ⊗ i₂ ⊗ i₃) = refl
  rev-rev assocr (i₁ ⊗ (i₂ ⊗ i₃)) = refl

  rev-rev′ : ∀ (r : Reshape s p) (i : P s) →  i ⟨ rev r ∙ r ⟩ ≡ i
  rev-rev′ eq i = refl
  rev-rev′ (r₁ ⊕ r₂) (i₁ ⊗ i₂) rewrite rev-rev′ r₁ i₁ | rev-rev′ r₂ i₂ = refl
  rev-rev′ (r₁ ∙ r₂) i rewrite rev-rev′ r₁ (i ⟨ rev r₂ ⟩) | rev-rev′ r₂ i = refl
  rev-rev′ swap (i₁ ⊗ i₂) = refl
  rev-rev′ assocl (i₁ ⊗ (i₂ ⊗ i₃)) = refl
  rev-rev′ assocr (i₁ ⊗ i₃ ⊗ i₂)   = refl

  reshape : Reshape s p → Ar s X → Ar p X
  reshape r a i = a (i ⟨ r ⟩)

  transp : S → S
  transp (ι n) = ι n
  transp (s ⊗ p) = transp p ⊗ transp s

  transpᵣ : Reshape (transp s) s
  transpᵣ {ι x} = eq
  transpᵣ {s ⊗ s₁} = (transpᵣ ⊕ transpᵣ) ∙ swap

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

  infixl 4 _⊡_
  _⊡_ = trans

  resh-rev : (r : Reshape s p) → ∀ i → i ⟨ rev r ⟩ ⟨ r ⟩ ≡ i
  resh-rev eq i = refl
  resh-rev (r ⊕ r₁) (i ⊗ j) rewrite resh-rev r i | resh-rev r₁ j = refl
  resh-rev (r ∙ r₁) i rewrite resh-rev r (i ⟨ rev r₁ ⟩) = resh-rev r₁ i
  resh-rev swap (i ⊗ j) = refl
  resh-rev assocl (i ⊗ (i₁ ⊗ i₂)) = refl
  resh-rev assocr (i ⊗ i₂ ⊗ i₁) = refl
 
  rev-fact : (r : Reshape s p) → ∀ i j → i ⟨ rev r ⟩ ≡ j → i ≡ j ⟨ r ⟩
  rev-fact r i j e = sym (resh-rev r i) ⊡ cong (_⟨ r ⟩) e

module D (U : Set) (El : U → Set) where

  open A U El

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


module F (U : Set) (El : U → Set) where

  open A U El

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
      -- b = map (ufft dft twid) (nest (reshape swap a))
      -- c = unnest (λ i → zipWith _*ᶜ_ (twid i) (b i)) 
      -- Localising twiddling:
      c = unnest $ imap 
          (λ i → zipWith _*ᶜ_ (twid {p} {s} i) ∘ ufft {s} dft twid) 
        (nest (reshape swap a))
      d = map (ufft {p} dft twid) (nest (reshape swap c))
    in (unnest d)

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

  vmap : (f : Ar p X → Ar p Y) → (Reshape s (s′ ⊗ V)) → Ar (s ⊗ p) X → Ar (s ⊗ p) Y
  vmap f r xs = let 
      a = nest $ reshape r $ nest xs
      b = map (map f) a
      c = unnest $ reshape (rev r) $ unnest b
    in c

  dftVec :  (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ) 
            → Ar (V ⊗ ι n) ℂ
            → Ar (V ⊗ ι n) ℂ
  dftVec dft xs = unnest (map dft (nest xs))

  ufft-vec₁ : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
         (twid : ∀ {s p} → P s → P p → ℂ)
       → VEC V s
       → Ar s ℂ → Ar s ℂ

  mapVec₁ : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
           (twid : ∀ {s p} → P s → P p → ℂ)
           → VEC V (s ⊗ p)
           → Ar (s ⊗ p) ℂ 
           → Ar (s ⊗ p) ℂ
  mapVec₁ {V} {s} {ι n} dft twid (vec₁ ⊗ ι r) xs = 
    let
      a = nest $ reshape (assocr ∙ pull-Vᵣ vec₁ ⊕ eq) xs
      b = map (dftVec dft) a
      c = reshape (rev (assocr ∙ pull-Vᵣ vec₁ ⊕ eq)) (unnest b)
    in c
  mapVec₁ {V} {s} {.(_ ⊗ _)} dft twid (vec₁ ⊗ (vec₂ ⊗ vec₃)) xs =
      unnest $ map (ufft-vec₁ dft twid (vec₂ ⊗ vec₃) ) (nest xs)

  ufft-vec₁ {V} {A.ι n  } dft twid vec = dft
  ufft-vec₁ {V} {s A.⊗ p} dft twid (vec₁ ⊗ vec₂) a =
    let 
      b = nest $ mapVec₁ dft twid (vec₂ ⊗ vec₁) (reshape swap a)
      c = unnest (λ i → zipWith _*ᶜ_ (twid i) (b i)) 
      d = mapVec₁ dft twid (vec₁ ⊗ vec₂) (reshape swap c)
    in d

  -----------------------------------------------------------------------------
  ufft-vec₂ : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
         (twid : ∀ {s p} → P s → P p → ℂ)
       → VEC V s
       → Ar s ℂ → Ar s ℂ

  mapVec₂ : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
           (twid : ∀ {s p} → P s → P p → ℂ)
           → VEC V (s ⊗ p)
           → Ar (s ⊗ p) ℂ 
           → Ar (s ⊗ p) ℂ
  mapVec₂ {V} {s} {ι n} dft twid (vec₁ ⊗ ι r) xs = 
    let
      a = nest $ reshape (assocr ∙ pull-Vᵣ vec₁ ⊕ eq) xs
      b = map (dftVec dft) a
      c = reshape (rev (assocr ∙ pull-Vᵣ vec₁ ⊕ eq)) (unnest b)
    in c
  mapVec₂ {V} {s} {.(_ ⊗ _)} dft twid (vec₁ ⊗ (vec₂ ⊗ vec₃)) xs =
      unnest $ map (ufft-vec₂ dft twid (vec₂ ⊗ vec₃) ) (nest xs)

  mapTwid₂ : (twid : ∀ {s p} → P s → P p → ℂ)
           → VEC V (s ⊗ p)
           → Ar (s ⊗ p) ℂ
           → Ar (s ⊗ p) ℂ
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

  ufft-vec₂ {V} {A.ι n  } dft twid vec = dft
  ufft-vec₂ {V} {s A.⊗ p} dft twid (vec₁ ⊗ vec₂) a =
    let 
      b = mapVec₂ dft twid (vec₂ ⊗ vec₁) (reshape swap a)
      c = mapTwid₂ twid (vec₂ ⊗ vec₁) b
      d = mapVec₂ dft twid (vec₁ ⊗ vec₂) (reshape swap c)
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
  mapVec₃ {V} {s} {ι n} dft twid true (vec₁ ⊗ ι r) xs = 
    let
      a = nest $ reshape (assocr ∙ pull-Vᵣ vec₁ ⊕ eq) xs
      b = map (dftVec dft) a
      c = imap (λ i → zipWith _*ᶜ_ (λ j → (unnest (twid {s} {ι n})) ((i ⊗ j) ⟨ assocr ∙ (pull-Vᵣ vec₁ ⊕ eq) ⟩ ))) b
      d = reshape (rev (assocr ∙ pull-Vᵣ vec₁ ⊕ eq)) (unnest c)
    in d
  mapVec₃ {V} {s} {ι n} dft twid false (vec₁ ⊗ ι r) xs = 
    let
      a = nest $ reshape (assocr ∙ pull-Vᵣ vec₁ ⊕ eq) xs
      b = map (dftVec dft) a
      c = reshape (rev (assocr ∙ pull-Vᵣ vec₁ ⊕ eq)) (unnest b)
    in c
  mapVec₃ {V} {s} {.(_ ⊗ _)} dft twid true vec@(vec₁ ⊗ (vec₂ ⊗ vec₃)) xs =
    let
      a = unnest $ map (ufft-vec₃ dft twid (vec₂ ⊗ vec₃) ) (nest xs)
      b = mapTwid₂ twid vec a
    in b
  mapVec₃ {V} {s} {.(_ ⊗ _)} dft twid false (vec₁ ⊗ (vec₂ ⊗ vec₃)) xs =
      unnest $ map (ufft-vec₃ dft twid (vec₂ ⊗ vec₃) ) (nest xs)

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
  
  ufft≡fft :   ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
             → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
             → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                         → ∀ i → dft {n} a i ≡ dft b i)
             → ∀ (xs : Ar s ℂ)
             → ∀ (i : P s) 
             →  ufft dft (λ i j → twid i (j ⟨ transpᵣ ⟩)) xs i
                ≡ 
                fft  dft twid xs ((A._⟨_⟩ U El i (A.transpᵣ U El)))
  ufft≡fft _ _ (A.ι _) = refl
  ufft≡fft dft-cong xs (i₁ A.⊗ j₁) = 
      (ufft-cong dft-cong _ _ (λ i₂ → cong₂ _*ᶜ_ refl (ufft≡fft dft-cong _ i₁)) j₁)
      ⊡
      (ufft≡fft dft-cong _ j₁)

  -----------------------------------------------------------------------------
  map-vec₁≡map-ufft :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                    → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                    → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                                → ∀ i → dft {n} a i ≡ dft b i)
                    → ∀ (vec : VEC V (s ⊗ p))
                    → ∀ (xs : Ar (s ⊗ p) ℂ)
                    → ∀ (i : P (s ⊗ p)) 
                    → mapVec₁ dft twid vec xs i ≡ unnest (map (ufft dft twid) (nest xs)) i

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
            → ∀ i → mapVec₁ dft twid v a i ≡ mapVec₁ dft twid v b i
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
                    → mapVec₂ dft twid vec xs i ≡ mapVec₁ dft twid vec xs i

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
        (reshape swap (zipWith _*ᶜ_ (unnest twid) (mapVec₂ dft twid (vec₂ ⊗ vec₁) (reshape swap xs))))
        (λ{(j₁ ⊗ j₂) → mapTwid₂-prop twid (vec₂ ⊗ vec₁) (mapVec₂ dft twid (vec₂ ⊗ vec₁) (reshape swap xs)) (j₂ ⊗ j₁) }) 
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
            → ∀ i → mapVec₂ dft twid v a i ≡ mapVec₂ dft twid v b i
  mapVec₂-cong dft-cong vec a b prf i = 
    map-vec₂≡map-vec₁ dft-cong vec _ i
    ⊡
    mapVec₁-cong dft-cong vec _ _ prf i 
    ⊡
    sym (map-vec₂≡map-vec₁ dft-cong vec _ i)

  -----------------------------------------------------------------------------
  map-vec₃≡map-vec₂-twid :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                          → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                          → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                                      → ∀ i → dft {n} a i ≡ dft b i)
                          → ∀ (vec : VEC V (s ⊗ p))
                          → ∀ (xs : Ar (s ⊗ p) ℂ)
                          → ∀ (i : P (s ⊗ p)) 
                          → mapVec₃ dft twid true vec xs i ≡ (mapTwid₂ twid vec (mapVec₂ dft twid vec xs)) i

  map-vec₃≡map-vec₂-¬twid :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                           → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                           → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                                       → ∀ i → dft {n} a i ≡ dft b i)
                           → ∀ (vec : VEC V (s ⊗ p))
                           → ∀ (xs : Ar (s ⊗ p) ℂ)
                           → ∀ (i : P (s ⊗ p)) 
                           → mapVec₃ dft twid false vec xs i ≡ mapVec₂ dft twid vec xs i
  map-vec₃≡map-vec₂-¬twid _ (vec₁ ⊗ ι x) xs (i₁ A.⊗ A.ι x₁) = refl
  map-vec₃≡map-vec₂-¬twid dft-cong vec@(vec₁ ⊗ (vec₂ ⊗ vec₃)) xs i@(i₁ A.⊗ (i₂ A.⊗ i₃)) 
      = map-vec₃≡map-vec₂-¬twid dft-cong (vec₂ ⊗ vec₃) _ (i₂ ⊗ i₃)
      ⊡ mapVec₂-cong dft-cong (vec₂ ⊗ vec₃) _ _ (λ{(j₁ ⊗ j₂) → 
          map-vec₃≡map-vec₂-twid dft-cong (vec₃ ⊗ vec₂) _ (j₂ ⊗ j₁)
        }) (i₂ ⊗ i₃)

  -- The below proof is stinky and there is probably a MUCH nicer way of doing
  -- it......... but it works
  map-vec₃≡map-vec₂-twid dft-cong (vec₁ ⊗ ι x) xs i@(i₁ ⊗ ι x₁) 
    with (((i₁ ⟨ rev (pull-Vᵣ vec₁) ⟩) ⊗ ι x₁) ⟨ assocl ⟩) 
  ... | j₁ ⊗ j₂ rewrite rev-rev (assocr ∙ pull-Vᵣ vec₁ ⊕ eq) (j₁ ⊗ j₂) = refl
  map-vec₃≡map-vec₂-twid {dft = dft} {twid = twid} dft-cong (vec₁ ⊗ (vec₂ ⊗ vec₃)) xs (i₁ ⊗ (i₂ ⊗ i₃)) 
  -- TODO: Improve at a later point - this with is foul
    with (((i₁ ⟨ rev (pull-Vᵣ vec₁) ⟩) ⊗ (i₂ ⊗ i₃)) ⟨ assocl ⟩)  
  ... | j₁ ⊗ j₂ with (((j₁ ⊗ j₂) ⟨ assocr ⟩) ⟨ pull-Vᵣ vec₁ ⊕ eq ⟩)
  ...           | j₃ ⊗ j₄
    = cong₂ _*ᶜ_ refl (
          (map-vec₃≡map-vec₂-¬twid 
            dft-cong 
            (vec₂ ⊗ vec₃) 
            (λ z → mapVec₃ dft twid true (vec₃ ⊗ vec₂) (λ z₁ → xs (j₃ ⊗ (z₁ ⟨ swap ⟩))) (z ⟨ swap ⟩)) 
            j₄
          )
          ⊡ mapVec₂-cong dft-cong (vec₂ ⊗ vec₃) _ _ (λ{(k₁ ⊗ k₂) → 
              map-vec₃≡map-vec₂-twid dft-cong (vec₃ ⊗ vec₂) _ (k₂ ⊗ k₁)
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
    map-vec₃≡map-vec₂-¬twid dft-cong vec _ (i₁ ⊗ i₂)
    ⊡
    mapVec₂-cong dft-cong vec _ _ (λ{ (j₁ ⊗ j₂) → 
      map-vec₃≡map-vec₂-twid dft-cong (vec₂ ⊗ vec₁) (reshape swap xs) (j₂ ⊗ j₁)
    }) (i₁ ⊗ i₂)

    

module T (U : Set) (El : U → Set) where

  private variable
    X Y : Set

  S₁ = A.S U El
  P₁ = A.P U El
  Ar₁ = A.Ar U El
 
  S₂ = A.S S₁ P₁
  P₂ = A.P S₁ P₁
  Ar₂ = A.Ar S₁ P₁

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

  module F₁ = F U El

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

  module F₂ = F S₁ P₁

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
               F.ufft (A.S U El) (A.P U El)
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

  S₁  = A.S  ℕ (Fin ∘ suc)
  P₁  = A.P  ℕ (Fin ∘ suc)
  Ar₁ = A.Ar ℕ (Fin ∘ suc)

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

  open Cplx cplx using (+-*-isCommutativeRing)
  open import Algebra.Structures as AlgebraStructures
  open AlgebraStructures {A = ℂ} _≡_
  open AlgebraStructures.IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid) renaming (*-comm to *𝕔-comm)

  module NEWFFT = F ℕ (Fin ∘ suc)
  module A′ = A ℕ (Fin ∘ suc)
  open B
  
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

  helper : iota 
            ((P₁-to-P₂ i₁ R.⟨ R.rev R.recursive-transposeᵣ ⟩) R.⟨ R.rev R.♭ ⟩) 
            ≡ 
           iota 
            (P₁-to-P₂ (i₁ A′.⟨ A′.transpᵣ ⟩) R.⟨ R.rev R.♭ ⟩)
  helper {A.ι _} {A.ι _} = refl
  helper {s₁ A.⊗ s₂} {i₁ A.⊗ i₂} = cong iota ? --cong (λ f → iota (f R.⟨ R.split ⟩)) ?

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
  
  open import Relation.Nullary
  open import Data.Empty
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
                        (helper {s₁} {i₁})
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


