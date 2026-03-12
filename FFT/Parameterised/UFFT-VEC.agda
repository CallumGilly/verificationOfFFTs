{-# OPTIONS --allow-unsolved-metas #-}
open import Complex using (Cplx)
open import Matrix.Mon


module FFT.Parameterised.UFFT-VEC (cplx : Cplx) (M : Mon) where

open Cplx cplx using (ℂ) renaming (_*_ to _*ᶜ_)

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Fin as Fin hiding (raise)
open import Data.Bool
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong; dcong₂)
open Eq.≡-Reasoning
--open Eq.Properties
open import Function
open import Algebra.Definitions

open import Data.Unit
-- This gives a warn on older versions of Agda when Product doesnt have a zipWith method
open import Data.Product hiding (swap; map; map₁; map₂; zipWith)
open import Data.Product.Properties
open import Data.Sum as Sum hiding (swap; map)

--postulate
--  ℂ : Set
--  _*ᶜ_ : ℂ → ℂ → ℂ

private
  infixl 4 _⊡_
  _⊡_ = trans


open import Matrix.Parameterised M
open import Matrix.Parameterised.Levels
open import FFT.Parameterised.FFT cplx M
open import FFT.Parameterised.UFFT cplx M


open Mon M using (U; El)
--open A M
open PL M

private
  variable
    s p V : S
    n : U
    X Y Z : Set

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

{-
  Could be nice, given cong on f and g as args
vecPattern₁-cong : 
            ∀ {s p : S}
          → (vec : VEC V (s ⊗ p))
          → (f  : ∀ {n} → P (pull-V (vec-fst vec)) → Ar (V ⊗ ι n) X → Ar (V ⊗ ι n) Z)
          → (g  : VEC V      p  → Ar p X       → Ar p Y      )
          → (g′ : VEC V (s ⊗ p) → Ar (s ⊗ p) Y → Ar (s ⊗ p) Z) 
          → ∀ a b → (∀ i → a i ≡ b i)
          → ∀ i → vecPattern vec f g g′ a i ≡ vecPattern vec f g g′ b i
-}
id₁ : X → Y → Y
id₁ = λ _ → id


-- We want to trainsition away from copying this out in the form
-- V ⊗ s, and instead copy out sᵗ ⊗ V
-- First step -- 
dftVec :  (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ) 
          → Ar (V ⊗ ι n) ℂ
          → Ar (V ⊗ ι n) ℂ
dftVec dft xs = unnest (map dft (nest xs))

post-ufft-vec₁ : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
       (twid : ∀ {s p} → P s → P p → ℂ)
     → VEC V s
     → Ar s ℂ → Ar s ℂ
post-ufft-vec₁ {V} {ι n  } dft twid vec = dft
post-ufft-vec₁ {V} {s ⊗ p} dft twid (vec₁ ⊗ vec₂) a =
  let 
    b = nest $ vecPattern 
                  (vec₂ ⊗ vec₁) 
                  (λ _ → (dftVec dft)) 
                  (post-ufft-vec₁ dft twid) 
                  id₁ 
                  (reshape swap a)
    c = unnest (λ i → zipWith _*ᶜ_ (twid i) (b i)) 
    --d = mapVec₁ dft (post-ufft-vec₁ dft twid) (vec₁ ⊗ vec₂) (reshape swap c)
    d = vecPattern
                  (vec₁ ⊗ vec₂)
                  (λ _ → (dftVec dft)) 
                  (post-ufft-vec₁ dft twid) 
                  id₁ 
                  (reshape swap c)
  in d

pre-ufft-vec₁ : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
       (twid : ∀ {s p} → P s → P p → ℂ)
     → VEC V s
     → Ar s ℂ → Ar s ℂ
pre-ufft-vec₁ {V} {ι n  } dft twid vec = dft
pre-ufft-vec₁ {V} {s ⊗ p} dft twid (vec₁ ⊗ vec₂) a =
  let 
    b = nest $ vecPattern 
                  (vec₁ ⊗ vec₂) 
                  (λ _ → (dftVec dft)) 
                  (pre-ufft-vec₁ dft twid) 
                  id₁ 
                  a
    c = unnest (λ i → zipWith _*ᶜ_ (twid i) (b i)) 
    d = vecPattern
                  (vec₂ ⊗ vec₁)
                  (λ _ → (dftVec dft)) 
                  (pre-ufft-vec₁ dft twid) 
                  id₁ 
                  (reshape swap c)
  in reshape swap d

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
mapTwid₂-prop twid (vec₁ ⊗ vec₂) xs (i₁ ⊗ i₂)
  with (i₁ ⟨ rev (pull-Vᵣ vec₁) ⟩) | Eq.inspect (i₁ ⟨_⟩) (rev (pull-Vᵣ vec₁))
... | k ⊗ l | Eq.[ e ] rewrite sym (rev-fact (pull-Vᵣ vec₁) _ _ e) = refl


post-ufft-vec₂ : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
       (twid : ∀ {s p} → P s → P p → ℂ)
     → VEC V s
     → Ar s ℂ → Ar s ℂ
post-ufft-vec₂ {V} {ι n  } dft twid vec = dft
post-ufft-vec₂ {V} {s ⊗ p} dft twid (vec₁ ⊗ vec₂) a =
  let 
    b = vecPattern 
          (vec₂ ⊗ vec₁) 
          (λ _ → (dftVec dft)) 
          (post-ufft-vec₂ dft twid) 
          id₁ 
          (reshape swap a)
    c = mapTwid₂ twid (vec₂ ⊗ vec₁) b
    d = vecPattern
          (vec₁ ⊗ vec₂)
          (λ _ → (dftVec dft)) 
          (post-ufft-vec₂ dft twid) 
          id₁ 
          (reshape swap c)
  in d

-----------------------------------------------------------------------------
post-ufft-vec₃ : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
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
          (post-ufft-vec₃ dft twid)
          (if twiddle? then mapTwid₂ twid else id₁)
          xs

post-ufft-vec₃ {V} {ι n  } dft twid vec = dft
post-ufft-vec₃ {V} {s ⊗ p} dft twid (vec₁ ⊗ vec₂) a =
  let 
    b = mapVec₃ dft twid true  (vec₂ ⊗ vec₁) (reshape swap a)
    c = mapVec₃ dft twid false (vec₁ ⊗ vec₂) (reshape swap b)
  in c
-----------------------------------------------------------------------------

mapVec₁ : (dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ)
         → (ufft-vec : VEC V p → Ar p ℂ → Ar p ℂ)
         → VEC V (s ⊗ p)
         → Ar (s ⊗ p) ℂ 
         → Ar (s ⊗ p) ℂ
mapVec₁ {V} dft ufft-vec vec xs = vecPattern vec (λ _ → (dftVec dft)) ufft-vec id₁ xs
-----------------------------------------------------------------------------

mapVec₁≡map-post-ufft :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                  → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                  → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                              → ∀ i → dft {n} a i ≡ dft b i)
                  → ∀ (vec : VEC V (s ⊗ p))
                  → ∀ (xs : Ar (s ⊗ p) ℂ)
                  → ∀ (i : P (s ⊗ p)) 
                  → mapVec₁ dft (post-ufft-vec₁ dft twid) vec xs i ≡ unnest (map (post-ufft dft twid) (nest xs)) i

post-ufft-vec₁≡post-ufft :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                            → ∀ i → dft {n} a i ≡ dft b i)
                → ∀ (vec : VEC V s)
                → ∀ (xs : Ar s ℂ)
                → ∀ (i : P s) 
                →  post-ufft-vec₁ dft twid vec xs i
                   ≡ 
                   post-ufft dft twid xs i

mapVec₁≡map-post-ufft dft-cong (vec₁ ⊗ ι x) xs (i ⊗ ι j)
  with (i ⟨ rev (pull-Vᵣ vec₁) ⟩) | Eq.inspect (i ⟨_⟩) (rev (pull-Vᵣ vec₁))
... | k ⊗ l | Eq.[ e ] rewrite sym (rev-fact (pull-Vᵣ vec₁) _ _ e) = refl
mapVec₁≡map-post-ufft dft-cong vec@(vec₁ ⊗ (vec₂ ⊗ vec₃)) xs (i ⊗ (i₁ ⊗ i₂)) = 
      post-ufft-vec₁≡post-ufft dft-cong (vec₂ ⊗ vec₃) (nest xs i) (i₁ ⊗ i₂)

post-ufft-vec₁≡post-ufft  _ (ι _) _ _ = refl
post-ufft-vec₁≡post-ufft dft-cong (vec₁ ⊗ vec₂) xs (i₁ ⊗ i₂) =
    (mapVec₁≡map-post-ufft dft-cong (vec₁ ⊗ vec₂) _ (i₁ ⊗ i₂))
    ⊡ 
    (post-ufft-cong dft-cong _ _ (λ j → 
      cong₂
        _*ᶜ_
        refl
        (mapVec₁≡map-post-ufft dft-cong (vec₂ ⊗ vec₁) _ (j ⊗ i₁))
    ) i₂)

mapVec₁-cong : {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
            {twid : ∀ {s p} → P s → P p → ℂ}
          → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                      → ∀ i → dft {n} a i ≡ dft b i)
          → ∀ {s p : S}
          → (v : VEC V (s ⊗ p))
          → ∀ a b → (∀ i → a i ≡ b i)
          → ∀ i → mapVec₁ dft (post-ufft-vec₁ dft twid) v a i ≡ mapVec₁ dft (post-ufft-vec₁ dft twid) v b i
mapVec₁-cong dft-cong vec a b prf i@(i₁ ⊗ i₂) =
  mapVec₁≡map-post-ufft dft-cong vec _ i
  ⊡
  post-ufft-cong dft-cong _ _ (λ i → prf (i₁ ⊗ i)) i₂
  ⊡
  sym (mapVec₁≡map-post-ufft dft-cong vec _ i)

pre-ufft-vec₁≡pre-ufft :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                            → ∀ i → dft {n} a i ≡ dft b i)
                → ∀ (vec : VEC V s)
                → ∀ (xs : Ar s ℂ)
                → ∀ (i : P s) 
                →  pre-ufft-vec₁ dft twid vec xs i
                   ≡ 
                   pre-ufft dft twid xs i

mapVec₁≡map-pre-ufft :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                  → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                  → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                              → ∀ i → dft {n} a i ≡ dft b i)
                  → ∀ (vec : VEC V (s ⊗ p))
                  → ∀ (xs : Ar (s ⊗ p) ℂ)
                  → ∀ (i : P (s ⊗ p)) 
                  → mapVec₁ dft (pre-ufft-vec₁ dft twid) vec xs i ≡ unnest (map (pre-ufft dft twid) (nest xs)) i
mapVec₁≡map-pre-ufft {_} {_} {_} {dft} dft-cong (vec₁ ⊗ ι x) xs (i ⊗ ι j) 
  with (i ⟨ rev (pull-Vᵣ vec₁) ⟩) | Eq.inspect (i ⟨_⟩) (rev (pull-Vᵣ vec₁))
... | k ⊗ l | Eq.[ e ] rewrite sym (rev-fact (pull-Vᵣ vec₁) _ _ e) = refl
mapVec₁≡map-pre-ufft {_} {_} {_} {dft} dft-cong vec@(vec₁ ⊗ (vec₂ ⊗ vec₃)) xs i@(i₁ ⊗ (i₂ ⊗ i₃)) = 
      pre-ufft-vec₁≡pre-ufft dft-cong (vec₂ ⊗ vec₃) (nest xs i₁) (i₂ ⊗ i₃)
  {-
    Feel like it may be easier to just... re do the proof as oppsed to 
    translating it to use the other proof
    cong (λ f → mapVec₁ dft f vec xs i) (pre-ufft≡post-ufft  ? ? )
  ⊡ mapVec₁≡map-post-ufft dft-cong vec xs i
  ⊡ ?
  -}

pre-ufft-vec₁≡pre-ufft dft-cong vec xs (ι x) = refl
pre-ufft-vec₁≡pre-ufft dft-cong (vec₁ ⊗ vec₂) xs (i₁ ⊗ i₂) = 
    (mapVec₁≡map-pre-ufft dft-cong (vec₂ ⊗ vec₁) _ (i₂ ⊗ i₁))
    ⊡ 
    (pre-ufft-cong dft-cong _ _ (λ j → 
      cong₂
        _*ᶜ_
        refl
        (mapVec₁≡map-pre-ufft dft-cong (vec₁ ⊗ vec₂) _ (j ⊗ i₂))
    ) i₁)


-----------------------------------------------------------------------------

mapVec₂≡mapVec₁ :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                  → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                  → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                              → ∀ i → dft {n} a i ≡ dft b i)
                  → ∀ (vec : VEC V (s ⊗ p))
                  → ∀ (xs : Ar (s ⊗ p) ℂ)
                  → ∀ (i : P (s ⊗ p)) 
                  → mapVec₁ dft (post-ufft-vec₂ dft twid) vec xs i ≡ mapVec₁ dft (post-ufft-vec₁ dft twid) vec xs i

post-ufft-vec₂≡post-ufft-vec₁ :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                            → ∀ i → dft {n} a i ≡ dft b i)
                → ∀ (vec : VEC V s)
                → ∀ (xs : Ar s ℂ)
                → ∀ (i : P s) 
                →  post-ufft-vec₂ dft twid vec xs i
                   ≡ 
                   post-ufft-vec₁ dft twid vec xs i

mapVec₂≡mapVec₁ dft-cong (vec₁ ⊗ ι x) xs (i₁ ⊗ ι x₁) = refl
mapVec₂≡mapVec₁ dft-cong (vec₁ ⊗ (vec₂ ⊗ vec₃)) xs (i₁ ⊗ (i₂ ⊗ i₃)) 
    = post-ufft-vec₂≡post-ufft-vec₁ dft-cong (vec₂ ⊗ vec₃) (nest xs i₁) (i₂ ⊗ i₃)

post-ufft-vec₂≡post-ufft-vec₁ dft-cong (ι x) xs i = refl
post-ufft-vec₂≡post-ufft-vec₁ {dft = dft} {twid = twid} dft-cong (vec₁ ⊗ vec₂) xs (i₁ ⊗ i₂) =
    (mapVec₂≡mapVec₁ dft-cong (vec₁ ⊗ vec₂) _ (i₁ ⊗ i₂))
    ⊡
    (mapVec₁-cong dft-cong (vec₁ ⊗ vec₂) _ 
      (reshape swap (zipWith _*ᶜ_ (unnest twid) (mapVec₁ dft (post-ufft-vec₂ dft twid) (vec₂ ⊗ vec₁) (reshape swap xs))))
      (λ{(j₁ ⊗ j₂) → mapTwid₂-prop twid (vec₂ ⊗ vec₁) (mapVec₁ dft (post-ufft-vec₂ dft twid) (vec₂ ⊗ vec₁) (reshape swap xs)) (j₂ ⊗ j₁) }) 
      (i₁ ⊗ i₂)
    )
    ⊡
    (mapVec₁-cong dft-cong (vec₁ ⊗ vec₂) _ _ (λ{(j₁ ⊗ j₂) → 
            cong₂
              _*ᶜ_
              refl
              (mapVec₂≡mapVec₁ dft-cong (vec₂ ⊗ vec₁) _ (j₂ ⊗ j₁)) 
    }) (i₁ ⊗ i₂))

mapVec₂-cong : {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
            {twid : ∀ {s p} → P s → P p → ℂ}
          → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                      → ∀ i → dft {n} a i ≡ dft b i)
          → ∀ {s p : S}
          → (v : VEC V (s ⊗ p))
          → ∀ a b → (∀ i → a i ≡ b i)
          → ∀ i → mapVec₁ dft (post-ufft-vec₂ dft twid) v a i ≡ mapVec₁ dft (post-ufft-vec₂ dft twid) v b i
mapVec₂-cong dft-cong vec _ _ prf i = 
  mapVec₂≡mapVec₁ dft-cong vec _ i
  ⊡
  mapVec₁-cong dft-cong vec _ _ prf i 
  ⊡
  sym (mapVec₂≡mapVec₁ dft-cong vec _ i)

-----------------------------------------------------------------------------
mapVec₃≡mapVec₂ :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
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
                            mapTwid₂ twid vec (mapVec₁ dft (post-ufft-vec₂ dft twid) vec xs) i
                          else
                            mapVec₁ dft (post-ufft-vec₂ dft twid) vec xs i
                          )

mapVec₃≡mapVec₂ _ false (_ ⊗ ι _) _ (_ ⊗ ι _) = refl
mapVec₃≡mapVec₂ dft-cong false (vec₁ ⊗ (vec₂ ⊗ vec₃)) _ (i₁ ⊗ (i₂ ⊗ i₃)) 
    = mapVec₃≡mapVec₂ dft-cong false (vec₂ ⊗ vec₃) _ (i₂ ⊗ i₃)
    ⊡ mapVec₂-cong dft-cong (vec₂ ⊗ vec₃) _ _ (λ{(j₁ ⊗ j₂) → 
        mapVec₃≡mapVec₂ dft-cong true (vec₃ ⊗ vec₂) _ (j₂ ⊗ j₁)
      }) (i₂ ⊗ i₃)
mapVec₃≡mapVec₂ dft-cong true (vec ⊗ ι _) xs (i ⊗ ι x) 
  with (((i ⟨ rev (pull-Vᵣ vec) ⟩) ⊗ ι x) ⟨ assocl ⟩) 
... | j₁ ⊗ j₂ rewrite rev-eq (assocr ∙ pull-Vᵣ vec ⊕ eq) (j₁ ⊗ j₂) = refl
mapVec₃≡mapVec₂ dft-cong true (vec₁ ⊗ (vec₂ ⊗ vec₃)) xs (i₁ ⊗ (i₂ ⊗ i₃)) 
-- TODO: Improve.... more.....
--  with ((i₁ ⊗ (i₂ ⊗ i₃)) ⟨ (rev (assocr ∙ (pull-Vᵣ vec₁) ⊕ eq )) ⟩) 
--     | (((i₁ ⊗ (i₂ ⊗ i₃)) ⟨ (rev (assocr ∙ (pull-Vᵣ vec₁) ⊕ eq )) ⟩) ⟨ assocr ∙ pull-Vᵣ vec₁ ⊕ eq ⟩)
--... | j₁ ⊗ j₂ | j₃ ⊗ j₄ 
 with ((i₁ ⊗ (i₂ ⊗ i₃)) ⟨ (rev (assocr ∙ (pull-Vᵣ vec₁) ⊕ eq )) ⟩)  
... | j₁ ⊗ j₂ with ((j₁ ⊗ j₂) ⟨ assocr ∙ pull-Vᵣ vec₁ ⊕ eq ⟩)
...           | j₃ ⊗ j₄
  = cong₂ _*ᶜ_ refl (
        (mapVec₃≡mapVec₂
          dft-cong 
          false
          (vec₂ ⊗ vec₃) 
          (λ z → mapVec₃ _ _ true (vec₃ ⊗ vec₂) (λ z₁ → xs (j₃ ⊗ (z₁ ⟨ swap ⟩))) (z ⟨ swap ⟩)) 
          j₄
        )
        ⊡ mapVec₂-cong dft-cong (vec₂ ⊗ vec₃) _ _ (λ{(k₁ ⊗ k₂) → 
            mapVec₃≡mapVec₂ dft-cong true (vec₃ ⊗ vec₂) _ (k₂ ⊗ k₁)
          }) j₄
        )

post-ufft-vec₃≡post-ufft-vec₂ :  ∀ {dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ}
                → ∀ {twid : ∀ {s p} → P s → P p → ℂ}
                → (dft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) 
                            → ∀ i → dft {n} a i ≡ dft b i)
                → ∀ (vec : VEC V s)
                → ∀ (xs : Ar s ℂ)
                → ∀ (i : P s) 
                →  post-ufft-vec₃ dft twid vec xs i
                   ≡ 
                   post-ufft-vec₂ dft twid vec xs i
post-ufft-vec₃≡post-ufft-vec₂ dft-cong vec xs (ι x) = refl
post-ufft-vec₃≡post-ufft-vec₂ dft-cong vec@(vec₁ ⊗ vec₂) xs (i₁ ⊗ i₂) =
  mapVec₃≡mapVec₂ dft-cong false vec _ (i₁ ⊗ i₂)
  ⊡
  mapVec₂-cong dft-cong vec _ _ (λ{ (j₁ ⊗ j₂) → 
    mapVec₃≡mapVec₂ dft-cong true (vec₂ ⊗ vec₁) (reshape swap xs) (j₂ ⊗ j₁)
  }) (i₁ ⊗ i₂)
