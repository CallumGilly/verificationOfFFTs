
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

  vtwid : Ar ((s ⊗ p) ⊗ ι V) ℂ 
  vtwid {s} {p} ((i ⊗ j) ⊗ l) with nonZeroDec ((s ⊗ p) ⊗ ι V)
  ... | no ¬nz = ⊥-elim (zs-nopos ¬nz ((i ⊗ j) ⊗ l))
  ... | yes nz = -ω (length ((s ⊗ p) ⊗ ι V)) ⦃ nonZeroₛ-s⇒nonZero-s nz ⦄ (preoffset-prod (i ⊗ (j ⊗ l)))

  vdft : Ar (ι N ⊗ ι V) ℂ → Ar (ι N ⊗ ι V) ℂ
  vdft {N} _  _ with nonZero? N
  vdft {_} _  (ι j ⊗ _) | no ¬nz = ⊥-elim (¬nz (fin-nz _ j))
  vdft {N} xs (  j ⊗ l) | yes nz = sum (λ k → xs (k ⊗ l) * -ω N ⦃ nz ⦄ (iota k *ₙ iota j))

  vfft : Ar (s ⊗ ι V) ℂ → Ar (s ⊗ ι V) ℂ
  vfft {ι x} = vdft
  vfft {s ⊗ s₁} xs = let
      b = (unnest ∘ (mapLeft (nest ∘ vfft ∘ unnest)) ∘ nest ∘ reshape (swap ⊕ eq)) xs
      c = zipWith _*_ b vtwid
      d = (unnest ∘ (mapLeft (nest ∘ vfft ∘ unnest)) ∘ nest ∘ reshape (swap ⊕ eq)) c
    in d


  {-
  data ?SIMD : Shape → Set where
    ι : ?SIMD (ι V)
--    -⊗ : ?SIMD s → ?SIMD (s ⊗ p)
    ⊗- : ?SIMD p → ?SIMD (s ⊗ p)

  --- A plan should be a tree of simdifiable sub trees
  data Plan : Shape → Set where
    ⟱   : ?SIMD s     → Plan s -- When we do want to use SIMD
    --⟱   : ((ι V) ⊂ s) → Plan s -- When we do want to use SIMD
    --↓   :               Plan s -- When we don't
    _⊗_ : Plan s → Plan p → Plan (s ⊗ p)
    
  -- With the above definition of Plan, there are allot of ways we can chose to 
  --break down our subtrees, and once we are in a "SIMD Enviroment" we can't leave it
  --_ : Plan ((ι V ⊗ ι 3) ⊗ (ι 2 ⊗ (ι 3 ⊗ ι V)))
  -- SIMD on the left subtree, then no SIMD on the right, then SIMD on the right right subtree
  --_ = ⟱ (left idh) ⊗ (↓ ⊗ ⟱ (right idh))
  -- SIMD on the left subtree, and the right subtree
  --_ = ⟱ (left idh) ⊗ ⟱ (right (srt (right idh)))
  -- SIMD on the left subshape only
  --_ = (⟱ (left idh)) ⊗ ↓
  -- No SIMD at all:
  --_ = ↓
  -- SIMD Everywhere
  --_ = ⟱ (left (srt (left idh)))
  -- OR
  --_ = ⟱ (right (srt (right (srt (right idh)))))

  --tmp : (ιv⊂s : (ι V) ⊂ s) → Ar s ℂ → Ar ((inv-⊂ ιv⊂s) ⊗ ι V) ℂ
  tmp₂ : (ιv⊂s : (ι V) ⊂ s) → Reshape s (inv-⊂ ιv⊂s ⊗ ι V)

  offt : Plan s → Ar s ℂ → Ar s ℂ
  offt {s} ↓ xs = ?
  offt {s} (⟱ x) xs = ?
  offt {.(_ ⊗ _)} (p ⊗ p₁) xs = ?
  -}


  data ?SIMD : Shape → Set where
    ι : ?SIMD (ι V)
    _⊗_ : ?SIMD p → ?SIMD (s ⊗ p)
    _⊗₂_ : ?SIMD s → ?SIMD (s ⊗ p)

  data ?rSIMD : Shape → Set where
    ι : ?rSIMD (s ⊗ ι V)
    _⊗_ : ?rSIMD s → ?rSIMD p → ?rSIMD (s ⊗ p)

  private variable
    s₁ s₂ : Shape

  foo : ?SIMD (s₁ ⊗ s₂) → ∃[ p ] Reshape (p ⊗ ι V) (s₁ ⊗ s₂)
  foo {s₁} {s₂} (_⊗_ ι) = s₁ , eq
  foo {s₁} {s₂} (_⊗_ (_⊗_ x)) = ?


  data Plan : Shape → Set where
    ⟱ : ?SIMD s → Plan s
    _⊗_ : Plan s → Plan p → Plan (s ⊗ p)

  --offt : Plan s → Ar s ℂ → Ar s ℂ
  --offt (⟱ q) = ?
  --offt (p ⊗ p₁) xs i = ?

  otwid : Ar (s ⊗ p) ℂ 
  otwid {s} {p} (i ⊗ j) with nonZeroDec (s ⊗ p)
  ... | no ¬nz = ⊥-elim (zs-nopos ¬nz (i ⊗ j))
  ... | yes nz = -ω (length (s ⊗ p)) ⦃ nonZeroₛ-s⇒nonZero-s nz ⦄ (preoffset-prod (i ⊗ j))

  offt : ?rSIMD s → Ar s ℂ → Ar s ℂ
  offt ι = vfft
  offt {s₁ ⊗ s₂} (p₁ ⊗ p₂) xs = let
      b = (mapLeft (offt p₁) ∘ reshape swap) xs
      c = zipWith _*_ b otwid
      d = (mapLeft (offt p₂) ∘ reshape swap) c
    in d

  --vfft {s ⊗ s₁} xs = let
  --    b = (unnest ∘ (mapLeft (nest ∘ vfft ∘ unnest)) ∘ nest ∘ reshape (swap ⊕ eq)) xs
  --    c = zipWith _*_ b vtwid
  --    d = (unnest ∘ (mapLeft (nest ∘ vfft ∘ unnest)) ∘ nest ∘ reshape (swap ⊕ eq)) c
  --  in d







