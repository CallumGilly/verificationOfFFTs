open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Fin as Fin hiding (raise; lower)
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

open import Complex using (Cplx)

module _ (cplx : Cplx) where

open Cplx cplx using (ℂ) renaming (_*_ to _*ᶜ_)

--postulate
--  ℂ : Set
--  _*ᶜ_ : ℂ → ℂ → ℂ

private
  infixl 4 _⊡_
  _⊡_ = trans


open import Matrix.Parameterised.Mon


{-
module V (M : Mon) where
  open Mon M
  open import Matrix.Parameterised.Base M
  open import Matrix.Parameterised.Reshape M

  private
    variable
      n m : U
      s : S
      X : Set

  flat-P : P (ι n ⊗ ι m) → El (n ● m)
  flat-P (ι x₁ ⊗ ι x₂) = ((Inverse.from $ pair-law _ _) (x₁ , x₂))

  flatten-P : P s → El (size s)
  flatten-P (ι x) = x
  flatten-P (i₁ ⊗ i₂) = ((Inverse.from $ pair-law _ _) (flatten-P i₁ , flatten-P i₂))

  unflatten-P : El (size s) → P s
  unflatten-P {ι _} x = ι x
  unflatten-P {s₁ ⊗ s₂} x = let 
      l , r = (Inverse.to $ pair-law (size s₁) (size s₂)) x 
    in unflatten-P l ⊗ unflatten-P r

  P-inv₁ : ∀ {s} → ∀ i → unflatten-P {s} (flatten-P i) ≡ i
  P-inv₁ {.(ι _)} (ι x) = refl
  P-inv₁ {(s₁ ⊗ s₂)} (i₁ ⊗ i₂) = ?

  P-inv₂ : ∀ {s} → ∀ i → flatten-P {s} (unflatten-P i) ≡ i

  P↔El : El (size s) ↔ P s 
  Inverse.to P↔El = unflatten-P
  Inverse.from P↔El = flatten-P
  Inverse.to-cong P↔El = ?
  Inverse.from-cong P↔El = ?
  proj₁ (Inverse.inverse (P↔El {s})) refl = P-inv₁ {s} _
  proj₂ (Inverse.inverse (P↔El {s})) refl = P-inv₂ {s} _

  UVec : U → Set → Set
  UVec u X = El u → X
  

  Ar-to-UVec : ∀ {s : S} → Ar s X → UVec (size s) X
  Ar-to-UVec xs i = xs (unflatten-P i) --((ι i) ⟨ flatten ⟩)

  Ar-from-UVec : ∀ {s : S} → UVec (size s) X → Ar s X
  Ar-from-UVec xs i = xs (flatten-P i)

  inv₁ : ∀ (xs : Ar s X) → ∀ i → Ar-from-UVec {X} {s} (Ar-to-UVec xs) i ≡ xs i
  inv₁ {s} xs i rewrite P-inv₁ {s} i = refl 

  inv₂ : ∀ (xs : UVec (size s) X) → ∀ i → Ar-to-UVec {X} {s} (Ar-from-UVec xs) i ≡ xs i
  inv₂ {s} xs i rewrite P-inv₂ {s} i = refl 

  UVec↔Ar  : UVec (size s) X ↔ Ar s X
  Inverse.to UVec↔Ar = Ar-from-UVec
  Inverse.from UVec↔Ar = Ar-to-UVec
  Inverse.to-cong UVec↔Ar refl = refl
  Inverse.from-cong UVec↔Ar refl = refl
  -- Extensionally equal
  proj₁ (Inverse.inverse UVec↔Ar) refl = ? --inv₁
  proj₂ (Inverse.inverse UVec↔Ar) refl = ? --inv₂ 

  tm : ∀ {xs : Ar s X} → ∀ i → Ar-to-UVec xs (flatten-P i) ≡ xs i
  tm i rewrite P-inv₁ i = refl

  vecPrf⇒arPrf :  ∀ {xs ys : Ar s X} 
                  → (∀ i → Ar-to-UVec xs i ≡ Ar-to-UVec ys i)
                  → (∀ i → xs i ≡ ys i)
  vecPrf⇒arPrf prf i rewrite sym (P-inv₁ i) = prf (flatten-P i) 
  
  arPrf⇒vecPrf :  ∀ {xs ys : UVec (size s) X} 
                  → (∀ i → Ar-from-UVec {X} {s} xs i ≡ Ar-from-UVec ys i)
                  → (∀ i → xs i ≡ ys i)
  arPrf⇒vecPrf {s} prf i rewrite sym (P-inv₂ {s} i) = prf (unflatten-P i) 
-}

  -- Superseeded by module PL which operates more generally
  {-
  lower-S : S raise-M → S M₁
  lower-S (ι x) = x
  lower-S (s₁ ⊗ s₂) = lower-S s₁ ⊗ lower-S s₂

  lower-P : ∀ {s : S raise-M} → P raise-M s → P M₁ (lower-S s)
  lower-P (ι x) = x
  lower-P (i₁ ⊗ i₂) = lower-P i₁ ⊗ lower-P i₂

  raise-P : ∀ {s : S raise-M} → P M₁ (lower-S s) → P raise-M s
  raise-P {ι _} i = ι i
  raise-P {s₁ ⊗ s₂} (i₁ ⊗ i₂) = raise-P i₁ ⊗ raise-P i₂

  P-inv₁ : ∀ {s : S raise-M} → ∀ i → lower-P {s} (raise-P i) ≡ i
  P-inv₁ {ι x} i = refl
  P-inv₁ {s₁ ⊗ s₂} (i₁ ⊗ i₂) rewrite
      P-inv₁ {s₁} i₁
    | P-inv₁ {s₂} i₂
    = refl
  
  lower-Ar :  ∀ {s : S raise-M}
            → ∀ {X : Set}
            → Ar raise-M s X 
            → Ar M₁ (lower-S s) X
  lower-Ar xs i = xs (raise-P i)
    
  raise-Ar :  ∀ {s : S raise-M}
            → ∀ {X : Set}
            → Ar M₁ (lower-S s) X
            → Ar raise-M s X 
  raise-Ar xs i = xs (lower-P i) 

  Ar-inv₁ : ∀ {s : S raise-M} → ∀ {X : Set} → ∀ {xs : Ar M₁ (lower-S s) X} → ∀ i → lower-Ar {s} (raise-Ar xs) i ≡ xs i
  Ar-inv₁ {s} i rewrite P-inv₁ {s} i = refl

  -- The set of all n+1 shapes where the subtree at each leaf is itself ι₁
  data S₂-is-S₁ : S raise-M → Set where
    ι   : (n : Mon.U M₁) → S₂-is-S₁ (ι (ι n))
    _⊗_ : {s₁ s₂ : S raise-M} → (S₂-is-S₁ s₁) → (S₂-is-S₁ s₂) → S₂-is-S₁ (s₁ ⊗ s₂)

  shp-map : S raise-M → (S M₁ → S M₁) → S raise-M
  shp-map (ι x) f = ι (f x)
  shp-map (s₁ ⊗ s₂) f = (shp-map s₁ f) ⊗ (shp-map s₂ f)

  shp-map-id : ∀ {s : S raise-M} → shp-map s id ≡ s
  shp-map-id {ι x} = refl
  shp-map-id {s₁ ⊗ s₂} rewrite
      shp-map-id {s₁}
    | shp-map-id {s₂}
    = refl

  resh-map : ∀ {s : S raise-M} 
           → ∀ {f : S M₁ → S M₁} 
           → ∀ (r : ∀ {p₁ : S M₁} → Reshape M₁ (f p₁) p₁) --(f p₁) p₁) 
           → P raise-M s
           → P raise-M (shp-map s f) 
  resh-map {ι _} r (ι i) = ι (_⟨_⟩ M₁ i r)
  resh-map {s₁ ⊗ s₂} r (i₁ ⊗ i₂) = (resh-map r i₁) ⊗ (resh-map r i₂)

  resh-map-id : ∀ {s : S raise-M} → Reshape raise-M s (shp-map s id)
  resh-map-id {s} rewrite shp-map-id {s} = eq 
  -}

module T (M₁ : Mon) where
  open Mon M₁ using (U; El)
  --open A M₁
  open import Matrix.Parameterised.Base

  private variable
    X Y : Set

  S₁ = S M₁
  P₁ = P M₁
  Ar₁ = Ar M₁

  M₂ : Mon
  M₂ = record {
      U    = S₁
    ; El   = P₁
    }

  S₂  = S  M₂
  P₂  = P  M₂
  Ar₂ = Ar M₂

  flat-shp : S₂ → S₁
  flat-shp (ι x) = x
  flat-shp (s ⊗ p) = flat-shp s ⊗ flat-shp p

  flat-pos : ∀ {s} → P₂ s → P₁ (flat-shp s)
  flat-pos (ι i) = i
  flat-pos (i ⊗ j) = flat-pos i ⊗ flat-pos j

  flat-pos' : ∀ {s} → P₁ (flat-shp s) → P₂ s
  flat-pos' {ι x} i = ι i
  flat-pos' {s ⊗ s₁} (i ⊗ i₁) = flat-pos' i ⊗ flat-pos' i₁

  flat-ar : ∀ {s} → Ar₂ s X → Ar₁ (flat-shp s) X
  flat-ar a i = a (flat-pos' i)

  flat-ar' : ∀ {s} → Ar₁ (flat-shp s) X → Ar₂ s X
  flat-ar' a i = a (flat-pos i)

  lift-ar : ∀ {s} → Ar₁ s X → Ar₂ (ι s) X
  lift-ar a (ι i) = a i

  flat-pos-pos' : ∀ {s} i → flat-pos {s} (flat-pos' i) ≡ i
  flat-pos-pos' {ι x} i = refl
  flat-pos-pos' {s ⊗ p} (i ⊗ i₁) 
    = cong₂ _⊗_ (flat-pos-pos' {s} i) (flat-pos-pos' {p} i₁)


  dft₁ : ∀ {n} → Ar₁ (ι n) ℂ → Ar₁ (ι n) ℂ
  twid₁ : ∀ {s p} → P₁ s → P₁ p → ℂ
  dft₁-cong : ∀ {n} a b → (∀ i → a i ≡ b i)
          → ∀ i → dft₁ {n} a i ≡ dft₁ b i

  import FFT.Parameterised.old.FFT as F
  --open import FFT.Parameterised.FFT M
  module F₁ = F cplx M₁

  post-ufft₁ : ∀ {s} → _ → _
  post-ufft₁ {s} = F₁.post-ufft {s} dft₁ twid₁

  fft₁ : ∀ {s} → _ → _
  fft₁ {s} = F₁.fft {s} dft₁ twid₁
  
  post-ufft₁-cong : ∀ {s} a b → (∀ i → a i ≡ b i)
             → ∀ i → post-ufft₁ {s} a i ≡ post-ufft₁ b i
  post-ufft₁-cong {s} a b pf = F₁.post-ufft-cong dft₁-cong a b pf 
  
  dft₂ : ∀ {n} → Ar₂ (ι n) ℂ → Ar₂ (ι n) ℂ
  dft₂ a = lift-ar (post-ufft₁ (flat-ar a))

  twid₂ : ∀ {s p} → P₂ s → P₂ p → ℂ
  twid₂ i j = twid₁ (flat-pos i) (flat-pos j)

  module F₂ = F cplx M₂

  post-ufft₂ : ∀ {s} → _ → _
  post-ufft₂ {s} = F₂.post-ufft {s} dft₂ twid₂

  fft₂ : ∀ {s} → _ → _
  fft₂ {s} = F₂.fft {s} dft₂ twid₂
  
  thm : ∀ {s} (a : Ar₂ s ℂ) 
      → ∀ i → flat-ar (post-ufft₂ a) i ≡ (post-ufft₁ (flat-ar a)) i
  thm {ι n} a (ι x) = refl
  thm {ι n} a (i ⊗ i₁) = refl
  thm {s ⊗ p} a (i ⊗ j) 
      rewrite thm (λ j₁ →
               twid₁ (flat-pos j₁) (flat-pos {s} (flat-pos' i)) *ᶜ
               F.post-ufft cplx M₂ --(S M₁) (P M₁)
               (λ a₁ → lift-ar (F₁.post-ufft dft₁ twid₁ (λ i₁ → a₁ (ι i₁))))
               (λ i₁ j₂ → twid₁ (flat-pos i₁) (flat-pos j₂))
               (λ j₂ → a (j₂ ⊗ j₁)) (flat-pos' i)) j
      = post-ufft₁-cong _ _ (λ k → cong₂ _*ᶜ_ 
                     (cong₂ twid₁ (flat-pos-pos' {p} k)
                                  (flat-pos-pos' {s} i))
                     (thm (λ j₂ → a (j₂ ⊗ flat-pos' k)) i)) j




import Matrix.Parameterised as MatrixParameterised

record Change-Major (M : Mon) : Set where
  open MatrixParameterised M
  open Mon M using (U; El)
  field
    change-major : ∀ {s : S} → Reshape (transp s) s

    change-major-transp : ∀ { s } → ∀ i → i ⟨ change-major {s} ∙ (rev transpᵣ) ⟩ ≡ i ⟨ transpᵣ ∙ (rev change-major) ⟩
    change-major-rev  : ∀ {s : S} → ∀ i → i ⟨ rev (change-major {s}) ∙ change-major ⟩  ≡ i ⟨ eq ⟩ 
    change-major-id : ∀ {u : U} {x : El u} → (ι x) ⟨ change-major ⟩ ≡ ι x
    

open import Matrix.Parameterised.Levels
import FFT.Parameterised.FFT as F

record dft-fft (M : Mon) (CM : Change-Major M) : Set₁ where
  --module FM = F M
  open MatrixParameterised M
  open Change-Major CM
  open Mon M 
  open PL M

  field
    vdft : ∀ {n : U} → (El n → ℂ) → (El n → ℂ)
    vdft-cong : ∀ {n} a b → (∀ i → a i ≡ b i) → ∀ i → vdft {n} a i ≡ vdft b i

    twiddles : ∀ {s p : S} → P s → P p → ℂ
    transp-twid : ∀ {s p} → ∀ {i j} → twiddles ((i ⟨ transpᵣ ⟩) ⟨ transpᵣ ⟩) j ≡ twiddles {s} {p} i j


    --size : S → U

    --flatten : ∀ {s : S} → Reshape s (ι (size s))

    prf :   ∀ {s : S}
          → ∀ (xs : Ar s ℂ)
          → ∀ (i : P s) 
          → raise-Ar (vdft (lower-Ar xs)) i
            ≡ 
            reshape change-major (F.vfft cplx M vdft twiddles xs) i

module LowerUFFT (M : Mon) (CM : Change-Major M) (rel : dft-fft M CM) where
  open Mon M
  open import Matrix.Parameterised M
  open import FFT.Parameterised.old.FFT cplx M
  open import FFT.Parameterised.FFT cplx M
  --open F M
  open PL M
  open Change-Major CM
  open dft-fft rel
  
  lowerUFFT : ∀ {s : S}
         → ∀ (xs : Ar s ℂ)
         → ∀ i
         → lower-Ar (reshape (change-major ∙ rev transpᵣ) (vpost-ufft vdft (λ j₁ j₂ → twiddles j₁ (j₂ ⟨ transpᵣ ⟩)) xs)) i 
         ≡ vdft (lower-Ar xs) i
  lowerUFFT {s} xs i = 
      vpost-ufft≡vfft {s} {vdft} {twiddles} vdft-cong xs ((raise-P i) ⟨ change-major ∙ rev transpᵣ ⟩)
    ⊡ 
      cong (vfft vdft twiddles xs) (rev-eq′ transpᵣ (raise-P i ⟨ change-major ⟩))
    ⊡ 
      sym (prf xs (raise-P i))
    ⊡ 
      cong (vdft (lower-Ar xs)) (inv₂ {s} i)

module X (M : Mon) (Pred : Mon.U M → Set) where
  open Mon M
  open import Matrix.Parameterised M
  open PL M
  
  private
    variable 
      u : U
      s p : S
  
  data All : S → Set where
    ι   : Pred u → All (ι u)
    _⊗_ : All s  → All p → All (s ⊗ p)

  vfftx : (all-P : All s) 
       → (dft : ∀ {n : U} → Pred n → (El n → ℂ)  → (El n → ℂ))
       → (twid : ∀ {s p} → P s → P p → ℂ)
       → Ar s ℂ → Ar (transp s) ℂ
  vfftx {ι x} (ι pred) dft twid = raise-Ar ∘ dft pred ∘ lower-Ar
  vfftx {s ⊗ p} (all-s ⊗ all-p) dft twid a =
    let 
      b = map (vfftx all-s dft twid) (nest (reshape swap a))
      c = unnest (λ i → zipWith _*ᶜ_ (twid i) (b i)) 
      d = map (vfftx all-p dft twid) (nest (reshape swap c))
    in reshape swap (unnest d)

  cong-vfftx : ∀ (all : All s) 
             → ∀ (dft : ∀ {n : U} → Pred n → (El n → ℂ)  → (El n → ℂ))
             → ∀ (twid : ∀ {s p} → P s → P p → ℂ)
             → ∀ (xs ys : Ar s ℂ)
             → (prf : ∀ i → xs i ≡ ys i)
             → ∀ i
             → vfftx all dft twid xs i ≡ vfftx all dft twid ys i

open import Matrix.Parameterised.RaiseM as SM

module L (M₁ : Mon) (CM₁ : Change-Major M₁) (rel : dft-fft M₁ CM₁) (CM₂ : Change-Major (SM.raise-M M₁)) where

  variable
    X Y : Set

  M₂ = SM.raise-M M₁

  open Mon M₁ using () renaming (U to U₁; El to El₁)
  open Mon M₂ using () renaming (U to U₂; El to El₂)

  --module FM₁ = F M₁
  --module FM₂ = F M₂

  open import Matrix.Parameterised M₂ using (ι; _⊗_) renaming
    ( S to S₂
    ; P to P₂ 
    ; Ar to Ar₂
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
    ; _∙_ to _∙₂_
    ; transp to transp₂
    ; eq to eq₂
    ; _⊕_ to _⊕₂_
    ; rev-eq′ to rev-eq′₂
    ; rev-eq to rev-eq₂
    ; flatten to flatten₂
    ; unflatten to unflatten₂
    ; reshape-is-RShp to reshape-is-RShp₂
    )
    
  open import Matrix.Parameterised M₁ using (ι; _⊗_) renaming
    ( S to S₁
    ; P to P₁ 
    ; Ar to Ar₁
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
    ; rev-eq′ to rev-eq′₁
    ; rev-eq to rev-eq₁
    ; flatten to flatten₁
    ; unflatten to unflatten₁
    ; reshape-is-RShp to reshape-is-RShp₁
    )

  open import Matrix.Parameterised using (S)

  open Change-Major CM₁ 
      using () 
      renaming ( change-major to change-major₁
               ; change-major-id to change-major-id₁
               )
  open Change-Major CM₂ 
      using () 
      renaming ( change-major to change-major₂
               ; change-major-id to change-major-id₂
               )
  
  --open SM M₁          renaming (resh-map to resh-map₂)
  --open SM M₂ using () renaming (resh-map to resh-map₂)
  open PL M₁ using ()
             renaming ( lower-S  to lower-S₁
                      ; lower-P  to lower-P₁
                      ; raise-P  to raise-P₁
                      ; lower-Ar to lower-Ar₁
                      ; raise-Ar to raise-Ar₁
                      )
  open PL M₂ using ()
             renaming ( lower-S  to lower-S₂
                      ; lower-P  to lower-P₂
                      ; raise-P  to raise-P₂
                      ; lower-Ar to lower-Ar₂
                      ; raise-Ar to raise-Ar₂
                      ; inv₁ to P₂-inv₁
                      ; inv₂ to P₂-inv₂
                      )
  open PLR M₂
            renaming ( _∙_ to _∙ₗ_
                     )

  --raise-lower-P₂ : 
  --                ∀ {s} 
  --              → ∀ (i : P₁ (lower-S₂ s)) 
  --              → lower-P₂ {s} (raise-P₂ i) ≡ i
  --raise-lower-P₂ {s} i = P₂-inv₂ {s} i
  --raise-lower-P₂ {ι x} i = refl
  --raise-lower-P₂ {s₁ ⊗ s₂} (i₁ ⊗ i₂) rewrite
  --    raise-lower-P₂ {s₁} i₁
  --  | raise-lower-P₂ {s₂} i₂ = refl

  --lower-P₂-raise-P₂-inv : ∀ {s : S₂} → ∀ {p : P₁ (lower-S₂ s)} → (lower-P₂ {s} (raise-P₂ p)) ≡ p
  --lower-P₂-raise-P₂-inv {ι x} {p} = refl
  --lower-P₂-raise-P₂-inv {s₁ ⊗ s₂} {p₁ ⊗ p₂} rewrite
  --    lower-P₂-raise-P₂-inv {s₁} {p₁}
  --  | lower-P₂-raise-P₂-inv {s₂} {p₂}
  --  = refl



  open dft-fft rel


  raised-pre-ufft : ∀ {s : U₂} → (El₂ s → ℂ) → (El₂ s → ℂ)
  raised-pre-ufft {s} xs = reshape₁ change-major₁ (F.vpre-ufft cplx M₁ ? (λ j₁ j₂ → twiddles (j₁ ⟨ transpᵣ₁ ⟩₁) j₂) (reshape₁ (rev₁ transpᵣ₁) xs))

  raised-fft : ∀ {s : U₂} → (El₂ s → ℂ) → (El₂ s → ℂ)
  raised-fft {s} = reshape₁ change-major₁ ∘ F.vfft cplx M₁ vdft twiddles

  lemma₁ : ∀ {s : S₁}
         → ∀ (xs : El₂ s → ℂ)
         → ∀ i
         → raised-pre-ufft xs i ≡ raised-fft xs i

  ufft₂ : ∀ {s : S₂}
        → (f : ∀ {n : U₂} → (El₂ n → ℂ) → (El₂ n → ℂ))
        → Ar₂ s ℂ → Ar₂ s ℂ
  ufft₂ f = F.vpost-ufft cplx M₂ f (λ j₁ j₂ → twiddles (lower-P₂ j₁) (lower-P₂ (j₂ ⟨ transpᵣ₂ ⟩₂))) 

  lemma₂ : ∀ {s : S₁}
         → (xs :  Ar₁ s ℂ)
         → ∀ i
         → lower-Ar₁ (reshape₁ (change-major₁ ∙₁ rev₁ transpᵣ₁) (F.vpost-ufft cplx M₁ vdft (λ j₁ j₂ → twiddles j₁ (j₂ ⟨ transpᵣ₁ ⟩₁)) xs)) i
         ≡ vdft (lower-Ar₁ xs) i

  helper₁ : ∀ (dft′ : {n : U₁} → (El₁ n → ℂ) → (El₁ n → ℂ))
          -- Will need this of course, but can assume for now
          --→ (dft≡fft : ?)
          → ∀ {s : S₁}
          → ∀ (xs : Ar₁ s ℂ)
          → ∀ i
          → reshape₁ (change-major₁ ∙₁ rev₁ transpᵣ₁) (F.vpost-ufft cplx M₁ dft′ (λ j₁ j₂ → twiddles j₁ (j₂ ⟨ transpᵣ₁ ⟩₁)) xs) i
          ≡ raise-Ar₁ (dft′ (lower-Ar₁ xs)) i

  lemma₃ : ∀ {s : S₂} 
         → ∀ (dft₀ : {n : U₁} → (El₁ n → ℂ) → (El₁ n → ℂ))
         → ∀ (dft₁ : {n : U₂} → (El₂ n → ℂ) → (El₂ n → ℂ))
         →   (dft-prf : ∀ {n : U₂} → ∀ (xs : El₂ n → ℂ) → ∀ i → dft₀ (lower-Ar₁ xs) (lower-P₁ i) ≡ dft₁ xs i )
         --→ ∀ (twid : ∀ {s p : S₁} → P₁ s → P₁ p → ℂ)
         → ∀ (xs : Ar₂ s ℂ)
         → ∀ (i : P₂ s) 
         → reshape₁ (change-major₁ ∙₁ rev₁ transpᵣ₁) (F.vpost-ufft cplx M₁ dft₀ (λ j₁ j₂ → twiddles           j₁  (          j₂  ⟨ transpᵣ₁ ⟩₁)) (lower-Ar₂ xs)) (lower-P₂ i)
         ≡ reshape₂ (change-major₂ ∙₂ rev₂ transpᵣ₂) (F.vpost-ufft cplx M₂ dft₁ (λ j₁ j₂ → twiddles (lower-P₂ j₁) ((lower-P₂ j₂) ⟨ transpᵣ₁ ⟩₁))            xs )           i 
  lemma₃ {ι n} dft₀ dft₁ dft-prf xs (ι x) rewrite 
      change-major-id₂ {_} {x}
    | helper₁ dft₀ (lower-Ar₂ xs) x 
    | dft-prf (lower-Ar₂ xs) x = refl
  lemma₃ {s ⊗ s₁} dft₀ dft₁ dft-prf xs (i₁ ⊗ i₂) = ?

  --data ι-Pred : U₂ → Set where
  --  ι : (u₁ : U₁) → ι-Pred (ι u₁)
  
  {-
    I find it weird but the function here fails, while the one below it 
    parses....
    
    -- Fails:
    SF : ∀ S₂ → Σ S₂ (λ s′ → All₂ ι-Pred s′)
    -- Correct:
    SF : ∀ (s : S₂) → Σ S₂ (λ s′ → All₂ ι-Pred s′)
  -}

  {-
  SF : ∀ (s : S₂) → Σ S₂ (All₂ ι-Pred)
  SF (ι n) = (ι (ι (A₁.size n))) , X.ι (ι (A₁.size n))
  SF (s₁ ⊗ s₂) = let
      p₁ , prf₁ = SF s₁
      p₂ , prf₂ = SF s₂
    in p₁ ⊗ p₂ , prf₁ All₂.⊗ prf₂
  -}

  {-
  data All-ι : S₂ → Set where
    ι   : ∀ (u : U₁) → All-ι (ι (ι u))
    _⊗_ : ∀ {s p : S₂} → All-ι s → All-ι p → All-ι (s ⊗ p)

  map-flat-S : S₂ → Σ S₂ All-ι 
  map-flat-S (ι x) = ι (ι (lower-S₁ x)) , ι (lower-S₁ x)
  map-flat-S (s₁ ⊗ s₂) = (map-flat-S s₁ .proj₁) ⊗ (map-flat-S s₂ .proj₁) , (map-flat-S s₁ .proj₂) ⊗ (map-flat-S s₂ .proj₂)

  lower-S-transp : ∀ {s : S₂} → transp₁ (lower-S₂ (map-flat-S s .proj₁)) ≡ lower-S₂ (transp₂ (map-flat-S s .proj₁))
  lower-S-transp {ι x} = refl
  lower-S-transp {s₁ ⊗ s₂} rewrite  
      lower-S-transp {s₁} 
    | lower-S-transp {s₂} 
    = refl

  level-Reshape : ∀ {s : S₂} → Reshape₁ 
                                (transp₁ (lower-S₂ (map-flat-S s .proj₁))) 
                                (lower-S₂ (transp₂ (map-flat-S s .proj₁)))
  level-Reshape {s} = subst (λ t → Reshape₁ (transp₁ (lower-S₂ (map-flat-S s .proj₁))) t) (lower-S-transp {s}) eq₁ 

  {-
  The idea here is that we can compare when all the leaves of S₂ are ι (prod s) 
  (i.e. all leaves of S₂ are flattened S₁'s) which means that the FFT is doing 
  the exact same in both cases
  -} 

  lemma₅ : ∀ {s : S₂}
         → ∀ (xs : Ar₂ (map-flat-S s .proj₁) ℂ)
         → ∀ i
         → F.vfft M₂ (raise-Ar₁ ∘ vdft ∘ lower-Ar₁) (λ j₁ j₂ → twiddles (lower-P₂ j₁) (lower-P₂ j₂)) xs i 
         ≡ (raise-Ar₂ (reshape₁ ({- level-Reshape {s} -} ?) (F.vfft M₁ vdft twiddles (lower-Ar₂ xs)))) i
  lemma₅ {ι x} xs (ι x₁) = refl
  lemma₅ {s₁ ⊗ s₂} xs (i₁ ⊗ i₂) = ?
    

  {-
  lemma₆ : ∀ {s : S₂}
         → ∀ (xs : Ar₂ (map-flat-S s .proj₁) ℂ)
         → ∀ i
         → reshape₂ transpᵣ₂ (F.vfft M₂ (raise-Ar₁ ∘ vdft ∘ lower-Ar₁) (λ j₁ j₂ → twiddles (lower-P₂ j₁) (lower-P₂ j₂)) xs) i 
         ≡ (raise-Ar₂ (reshape₁ transpᵣ₁ (F.vfft M₁ vdft twiddles (lower-Ar₂ xs)))) i
  lemma₆ {ι x} xs i = refl
  lemma₆ {s₁ ⊗ s₂} xs (i₁ ⊗ i₂) =
      lemma₆ {s₂} _ i₂
    ⊡ ?
  -}

  vdft₁ : ∀ {s : S₁} → Ar₁ s ℂ → Ar₁ s ℂ
  vdft₁ = raise-Ar₁ ∘ vdft ∘ lower-Ar₁

  twiddles₂ : ∀ {s p : S₂} → P₂ s → P₂ p → ℂ
  twiddles₂ j₁ j₂ = twiddles (lower-P₂ j₁) (lower-P₂ j₂)

  All-⊤ : ∀ {M : Mon} → {s : S M} → X.All M (λ _ → ⊤) s
  All-⊤ {_} {ι _} = X.ι tt
  All-⊤ {_} {_ ⊗ _} = All-⊤ X.⊗ All-⊤

  data ι-Pred : U₂ → Set where
    ι : (u₁ : U₁) → ι-Pred (ι u₁)

  open X M₂ renaming (All to All₂)

  SF : ∀ (s : S₂) → Σ S₂ (All₂ ι-Pred)
  SF (ι x) = ι (ι (lower-S₁ x)) , ι (ι (lower-S₁ x))
  SF (s₁ ⊗ s₂) = let
      p₁ , prf₁ = SF s₁
      p₂ , prf₂ = SF s₂
    in p₁ ⊗ p₂ , prf₁ All₂.⊗ prf₂

  PF : ∀ {s : S₂} → P₂ s → P₂ (SF s .proj₁)
  PF {ι _} (ι k) = ι (ι (lower-P₁ k)) 
  PF {_ ⊗ _} (i ⊗ j) = PF i ⊗ PF j

  PFᵣ : ∀ {s : S₂} → Reshapeℓ {ss} {ss} s (SF s .proj₁)
  PFᵣ {ι x} = lower ∙ₗ (resh-U {_} {_} {reshape-is-RShp₁} flatten₁) ∙ₗ raise 
  PFᵣ {s ⊗ s₁} = ?

  PF′ : ∀ {s : S₂} → P₂ (SF s .proj₁) → P₂ s
  PF′ {ι _} (ι (ι k)) = ι (raise-P₁ k)
  PF′ {_ ⊗ _} (i ⊗ j) = PF′ i ⊗ PF′ j

  ArF : ∀ {s : S₂} → Ar₂ s ℂ → Ar₂ (SF s .proj₁) ℂ
  ArF xs i = xs (PF′ i) 

  ArF′ : ∀ {s : S₂} → Ar₂ (SF s .proj₁) ℂ → Ar₂ s ℂ
  ArF′ xs i = xs (PF i)

  PFᵗᵣ : ∀ {s : S₂} → Reshape₂ (transp₂ s) (transp₂ (SF s .proj₁))
  PFᵗᵣ {ι x} = ?
  PFᵗᵣ {s₁ ⊗ s₂} = ?

  PFᵗ : ∀ {s : S₂} → P₂ (transp₂ s) → P₂ (transp₂ (SF s .proj₁))
  PFᵗ {ι x} (ι i) = PF (ι i)
  PFᵗ {s₁ ⊗ s₂} (i₁ ⊗ i₂) = (PFᵗ i₁) ⊗ (PFᵗ i₂)
  
  tmp : ∀ {s : S₂} → Reshape₂ (transp₂ s) (transp₂ (SF s .proj₁))
  tmp {ι x} = ?
  tmp {s ⊗ s₁} = ?

{-
  PF₃ : ∀ {s : S₂} → P₂ (transp₂ (SF s .proj₁)) → P₁ (transp₁ (lower-S₂ (SF s .proj₁ )))
  PF₃ {ι _} (ι x) = x
  PF₃ {s₁ ⊗ s₂} (i₁ ⊗ i₂) = (PF₃ {s₂} i₁) ⊗ (PF₃ {s₁} i₂)

  vfft₁≡vfftx₂-⊤ : ∀ {s : S₂} (xs : Ar₂ s ℂ) i
              → F.vfft M₂ vdft₁ twiddles₂ xs i ≡ X.vfftx M₂ (λ _ → ⊤) All-⊤ (λ _ → vdft₁) twiddles₂ xs i 

  vfftx₂-⊤≡vfftx₂-ι : ∀ {s : S₂} (xs : Ar₂ s ℂ) i
        → X.vfftx M₂ (λ _ → ⊤) All-⊤ (λ _ → vdft₁) twiddles₂ xs i 
        ≡ (X.vfftx M₂ ι-Pred (SF s .proj₂) (λ _ → vdft₁) twiddles₂ (ArF xs)) (PFᵗ i)

  vfftx₂-ι≡vfftx₁-⊤ : ∀ {s : S₂} (xs : Ar₂ s ℂ) i
           → (X.vfftx M₂ ι-Pred (SF s .proj₂) (λ _ → vdft₁) twiddles₂ (ArF xs)) i
           ≡ (X.vfftx M₁ (λ _ → ⊤) All-⊤ (λ _ → vdft) twiddles (lower-Ar₂ (ArF xs))) (PF₃ {s} i)
  vfftx₂-ι≡vfftx₁-⊤ {ι x} xs (ι x₁) = refl
  vfftx₂-ι≡vfftx₁-⊤ {s₁ ⊗ s₂} xs (i₁ ⊗ i₂) =
        vfftx₂-ι≡vfftx₁-⊤ {s₂} _ i₁
      ⊡ X.cong-vfftx M₁ (λ _ → ⊤) All-⊤ (λ _ → vdft) twiddles _ _ (λ j → cong₂ _*ᶜ_ ? (vfftx₂-ι≡vfftx₁-⊤ {s₁} ? i₂)) (PF₃ {s₂} i₁)

  vfftx₁-⊤≡vfft₁ : ∀ {s : S₂} (xs : Ar₂ s ℂ) i
                 → (X.vfftx M₁ (λ _ → ⊤) All-⊤ (λ _ → vdft) twiddles (lower-Ar₂ (ArF xs))) i
                 ≡ F.vfft M₁ vdft twiddles (lower-Ar₂ (ArF xs)) i

  help : {x : U₂} {x₁ : El₂ x} →
       lower-P₁ (PF₃ {ι x} (PFᵗ (ι x₁ ⟨ change-major₂ ⟩₂))) ≡ lower-P₁ x₁
  help {ι x} {ι x₁} rewrite change-major-id₂ {ι x} {ι x₁} = refl
  help {s₁ ⊗ s₂} {i₁ ⊗ i₂} rewrite change-major-id₂ {s₁ ⊗ s₂} {i₁ ⊗ i₂} = refl

  vfft₁-PF≡vfft₁ : {s : S₂} {xs : Ar₂ s ℂ} {i : P₂ s} →
                 F.vfft M₁ vdft twiddles (lower-Ar₂ (ArF xs))
                 (PF₃ {s} (PFᵗ (i ⟨ change-major₂ ⟩₂)))
                 ≡
                 raise-Ar₂
                 (reshape₁ change-major₁ (F.vfft M₁ vdft twiddles (lower-Ar₂ xs))) i
  vfft₁-PF≡vfft₁ {ι x} {xs} {ι x₁} = 
      cong (vdft (λ x₂ → xs (ι (raise-P₁ x₂)))) (help {x} {x₁})
    ⊡ (dft-fft.prf rel (lower-Ar₂ xs) (x₁))
  vfft₁-PF≡vfft₁ {s₁ ⊗ s₂} {xs} {i₁ ⊗ i₂} =
      ?

  
  vfft₂≡vfft₁ : {s : S₂} (xs : Ar₂ s ℂ) (i : P₂ s) →
              raise-Ar₂ (reshape₁ change-major₁ (F.vfft M₁ vdft twiddles (lower-Ar₂ xs))) i
              ≡
              reshape₂ 
                change-major₂ 
                (F.vfft 
                  M₂ 
                  (λ x → reshape₁ change-major₁ (F.vfft M₁ vdft twiddles x)) 
                  (λ j₁ j₂ → twiddles (lower-P₂ j₁) (lower-P₂ j₂)) 
                  xs
                ) 
                i
  vfft₂≡vfft₁ {s} xs i = sym 
    ( F.vfft-dft-cong M₂ _ _ xs (λ ys j → sym (dft-fft.prf rel ys j)) (i ⟨ change-major₂ ⟩₂) 
    ⊡ vfft₁≡vfftx₂-⊤ xs (i ⟨ change-major₂ ⟩₂)
    ⊡ vfftx₂-⊤≡vfftx₂-ι xs (i ⟨ change-major₂ ⟩₂)
    ⊡ vfftx₂-ι≡vfftx₁-⊤ {s} xs (PFᵗ (i ⟨ change-major₂ ⟩₂))
    ⊡ vfftx₁-⊤≡vfft₁ xs (PF₃ {s} (PFᵗ (i ⟨ change-major₂ ⟩₂)))
    ⊡ ? --vfft₁-PF≡vfft₁ 
    )

  transp-twid₂ : {s p : S₂} {i : P₂ s} {j : P₂ p} →
               twiddles (lower-P₂ ((i ⟨ transpᵣ₂ ⟩₂) ⟨ transpᵣ₂ ⟩₂)) (lower-P₂ j)
               ≡ twiddles (lower-P₂ i) (lower-P₂ j)
  transp-twid₂ {ι x} {p} {ι x₁} {j} = refl
  transp-twid₂ {s₁ ⊗ s₂} {p} {i₁ ⊗ i₂} {j} = ?

  ufft-is-vdft : dft-fft M₂ CM₂
  ufft-is-vdft = record {
      dft      = ? --raise-Ar₁ ∘ reshape₁ change-major₁ ∘ F.vfft M₁ ? ? ∘ lower-Ar₁
    ; dft-cong = ?
    ; vdft = reshape₁ change-major₁ ∘ F.vfft M₁ vdft twiddles
    ; vdft-cong = ?
    ; twiddles = λ j₁ j₂ → twiddles (lower-P₂ j₁) (lower-P₂ j₂)
    ; transp-twid = ?
    ; prf = vfft₂≡vfft₁
    }

  open LowerUFFT M₂ CM₂ ufft-is-vdft
  
  ufft₂≡ufft₁ : ∀ {s : S₂}
              → ∀ (xs : Ar₂ s ℂ)
              → ∀ i
              → lower-Ar₂ (reshape₂ (change-major₂ ∙₂ rev₂ transpᵣ₂) (ufft₂ (reshape₁ change-major₁ ∘ F.vfft M₁ vdft twiddles) xs)) i
              ≡ (reshape₁ (change-major₁ ∙₁ rev₁ transpᵣ₁) (F.vpost-ufft M₁ vdft (λ j₁ j₂ → twiddles j₁ (j₂ ⟨ transpᵣ₁ ⟩₁)) (lower-Ar₂ xs))) i
  ufft₂≡ufft₁ {s} xs i =
      lowerUFFT {s} _ i
    ⊡ 
      cong (F.vfft M₁ vdft twiddles (λ x → xs (PL.raise-P (SM.raise-M M₁) x))) (?)  --(rev-eq′₁ (?) (i ⟨ change-major₁ ⟩₁)) --(rev-eq′₁ transpᵣ₁ (i ⟨ change-major₁ ⟩₁))
    ⊡ 
      sym (F.vpost-ufft≡vfft M₁ {lower-S₂ s} {dft-fft.vdft rel} {twiddles} (dft-fft.vdft-cong rel) (lower-Ar₂ xs) (i ⟨ change-major₁ ∙₁ rev₁ transpᵣ₁ ⟩₁))

    --⊡ 
    --  ? --sym (F.vpost-ufft≡vfft M₁ {lower-S₂ s} {?} {?} ? ? ?)


-}
-}
