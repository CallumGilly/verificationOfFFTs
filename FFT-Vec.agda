
open import Real using (Real)
open import Complex using (Cplx)

import Algebra.Structures as AlgebraStructures

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

module FFT-Vec (cplx : Cplx) where
  open Cplx cplx

  open AlgebraStructures  {A = ℂ} _≡_
  open IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid)

  open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
  open import Data.Nat.Base renaming (_+_ to _+ₙ_; _*_ to _*ₙ_)
  open import Data.Nat.Properties 
  open import Relation.Nullary
  open import Data.Empty
  open import Data.Product hiding (swap; map)


  open import Matrix 
  open import Matrix.Sum _+_ 0ℂ +-isCommutativeMonoid using (sum)
  open import Matrix.Reshape 
  open import Matrix.NonZero 
  open import Matrix.SubShape

  open import Function

  private
    variable
      N : ℕ
      s p : Shape
    
  --- NonZero helpers

  fin-nz : (N : ℕ) → Fin N → NonZero N
  fin-nz (suc n) i = _

  pos⇒nz : Position s → NonZeroₛ s
  pos⇒nz (ι i) = ι (fin-nz _ i)
  pos⇒nz (i ⊗ i₁) = pos⇒nz i ⊗ pos⇒nz i₁

  zs-nopos : ¬ NonZeroₛ s → Position s → ⊥
  zs-nopos ¬nz-s (ι {suc n} i) = ¬nz-s (ι (fin-nz _ i))
  zs-nopos ¬nz-s (i ⊗ i₁) = ¬nz-s (pos⇒nz (i ⊗ i₁)) 

  ------------------------------------
  --- DFT and FFT helper functions ---
  ------------------------------------

  iota : Ar (ι N) ℕ
  iota (ι i) = toℕ i

---- XXX: Here is where we compute twiddles differently!
  preoffset-prod : Position (s ⊗ p) → ℕ
  preoffset-prod (k ⊗ j) = iota (k ⟨ ♯ ⟩) *ₙ iota (j ⟨ rev recursive-transposeᵣ ∙ ♯ ⟩)

  pretwiddles′ :  Ar (s ⊗ p) ℂ
  pretwiddles′ {s} {p} i with nonZeroDec (s ⊗ p)
  ... | no ¬nz = ⊥-elim (zs-nopos ¬nz i)
  ... | yes nz = -ω (length (s ⊗ p)) ⦃ nonZeroₛ-s⇒nonZero-s nz ⦄ (preoffset-prod i)

  V : ℕ
  V = 4

--First observation.  If we prevent inlining, we get exactly the pattern we wanted, i.e. applying dft over a dimension, and then doing the rest.  Here is a way to convince yourself:

  variable
    n : ℕ
    X Y : Set
    q : Shape

  postulate
    M : Set → Set
    _>>=_ : M X → (X → M Y) → M Y
    return : X → M X
    extract : M X → X
    dft : Ar (ι n) ℂ → Ar (ι n) ℂ
    twiddles′ : Ar (s ⊗ p) ℂ

--The above extract is bullshit in general, it is just to introduce a sequence of binds that is not normalised by Agda.

  mufft : ∀ {s} → Ar s ℂ → Ar s ℂ
  mufft {ι n} a = (dft a)
  mufft {s ⊗ p} a =
    extract (do
      b ← return (reshape swap (mapLeft mufft a))
      c ← return (zipWith _*_ b twiddles′)
      d ← return (reshape swap  (mapLeft mufft (c)))
      return d)

  {-
  --Pick arbitrary array, and normalise mufft application to it, you will see the right pattern.
  tmp : mufft {(ι 7 ⊗ ι V) ⊗ (ι 3 ⊗ ι 5)} ≡ ?
  tmp = ?
  -}


  data SIMD : Shape → Set where
    ι :  SIMD (ι V ⊗ s)
    _⊗_ : SIMD s → SIMD p → SIMD (s ⊗ p)

  data S : Shape → Shape → Shape → Set where
    ι : S (ι V) s (ι V ⊗ s)
    left : S (ι V) s p → S (ι V) (q ⊗ s) (q ⊗ p)
    right : S (ι V) s p → S (ι V) (s ⊗ q) (p ⊗ q)

  -- For a given shape s, which we know to hold the SIMD predicate
  -- there exists a shape x which does not contain one instance of
  -- the index (ι V)
  rem : SIMD s → ∃ λ x → S (ι V) x s
  rem {.(ι V ⊗ s)} (ι {s}) = s , ι
  rem (_⊗_ {_} {p} SIMD-s _) with rem SIMD-s
  ... | a , b = a ⊗ p , right b

  S-resh : S (ι V) p s → Reshape s (ι V ⊗ p)
  S-resh ι = eq
  S-resh (left  x) = assoₗ ∙ (swap ⊕ eq) ∙ assoᵣ ∙ eq ⊕ (S-resh x)
  S-resh (right x) = assoₗ ∙ (S-resh x) ⊕ eq

  comp-resh : (pr : SIMD s) → Reshape s (ι V ⊗ rem pr .proj₁)
  comp-resh = S-resh ∘ proj₂ ∘ rem
  --comp-resh pr with rem pr
  --comp-resh _ | _ , b = S-resh b
  -- Brother.......... you silly billy
  --comp-resh pr with rem pr
  --comp-resh ι | _ , b = S-resh b
  --comp-resh (SIMD-s ⊗ SIMD-p) | .(_ ⊗ _) , left  b =  S-resh (left b)
  --comp-resh (SIMD-s ⊗ SIMD-p) | .(_ ⊗ _) , right b = ?
  --comp-resh ι | ι _ , ι = eq
  --comp-resh ι | (s ⊗ p) , ι = eq
  --comp-resh ι | (.(ι V) ⊗ p) , left snd = ?
  --comp-resh (SIMD-s ⊗ SIMD-p) | fst , snd = ?
  
  trans-copy : Ar (ι V ⊗ s) (Ar p ℂ) → Ar s (Ar p (Ar (ι V) ℂ))
  trans-copy xs ps pp p4 = xs (p4 ⊗ ps) pp
  
  copy-trans : Ar s (Ar p (Ar (ι V) ℂ)) → Ar (ι V ⊗ s) (Ar p ℂ)
  copy-trans xs (p4 ⊗ ps) pp = xs ps pp p4

  ufft-vec : Ar s (Ar (ι V) ℂ) → Ar s (Ar (ι V) ℂ)
  --ufft-vec xs ps pv = mufft ((nest $ reshape swap $ unnest xs) pv) ps

  offt : ∀ {s} → SIMD s → Ar s ℂ → Ar s ℂ

  mapVec : SIMD (s ⊗ p) → Ar (s ⊗ p) ℂ → Ar (s ⊗ p) ℂ
  mapVec (p ⊗ ι) a = let
                        t = trans-copy (reshape (comp-resh p) (nest a))
                        w = Matrix.map ufft-vec t
                        q = reshape (rev (comp-resh p)) (copy-trans w)
                     in Matrix.unnest q
  mapVec (p ⊗ s@(s₁ ⊗ s₂)) a = mapLeft (offt s) a

  offt (ι ) a = reshape ♯ (dft (reshape ♭ a)) -- non-vectorised fft, whatever it is
  offt (s ⊗ p) a =
    extract (do
      b ← return (reshape swap (mapVec (s ⊗ p) a))
      c ← return (zipWith _*_ b twiddles′)
      d ← return (reshape swap  (mapVec (p ⊗ s) c))
      return d)

