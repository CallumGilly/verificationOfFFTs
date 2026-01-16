
open import Real using (Real)
open import Complex using (Cplx)

import Algebra.Structures as AlgebraStructures

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning



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
  open import Matrix.Equality

  open import Function

  open import FFT cplx 

  V : ℕ
  V = 4

  variable
    n : ℕ
    X Y : Set
    q s₁ s₂ : Shape


  ------------------------------------
  --- DFT and FFT helper functions ---
  ------------------------------------

---- XXX: Here is where we compute twiddles differently!
-- I want to investigate this further, for current tests ufft′ works with both 
-- versions of preoffset-prod, however, I feel that this may be a case of not 
-- trying at high enough dimensions

  offset-prod′ : Position (s ⊗ p) → ℕ
  offset-prod′ (k ⊗ j) = iota (k ⟨ ♯ ⟩) *ₙ iota (j ⟨ ♯ ⟩)

  preoffset-prod : Position (s ⊗ p) → ℕ
  preoffset-prod (k ⊗ j) = iota (k ⟨ ♯ ⟩) *ₙ iota (j ⟨ rev recursive-transposeᵣ ∙ ♯ ⟩)

  preoffset-prod′ : Position (s ⊗ p) → ℕ
  preoffset-prod′ (k ⊗ j) = iota (k ⟨ rev recursive-transposeᵣ ∙ ♯ ⟩) *ₙ iota (j ⟨ ♯ ⟩)

  pretwiddles :  Ar (s ⊗ p) ℂ
  pretwiddles {s} {p} i with nonZeroDec (s ⊗ p)
  ... | no ¬nz = ⊥-elim (zs-nopos ¬nz i)
  ... | yes nz = -ω (length (s ⊗ p)) ⦃ nonZeroₛ-s⇒nonZero-s nz ⦄ (preoffset-prod i)

  pretwiddles′ :  Ar (s ⊗ p) ℂ
  pretwiddles′ {s} {p} i with nonZeroDec (s ⊗ p)
  ... | no ¬nz = ⊥-elim (zs-nopos ¬nz i)
  ... | yes nz = -ω (length (s ⊗ p)) ⦃ nonZeroₛ-s⇒nonZero-s nz ⦄ (preoffset-prod i)

  twiddles′ : Ar (s ⊗ p) ℂ
  twiddles′ {s} {p} i with nonZeroDec (s ⊗ p)
  ... | no ¬nz = ⊥-elim (zs-nopos ¬nz i)
  ... | yes nz = -ω (length (s ⊗ p)) ⦃ nonZeroₛ-s⇒nonZero-s nz ⦄ (offset-prod i)

--First observation.  If we prevent inlining, we get exactly the pattern we wanted, i.e. applying dft over a dimension, and then doing the rest.  Here is a way to convince yourself:

  {-
  postulate
    M : Set → Set
    _>>=_ : M X → (X → M Y) → M Y
    return : X → M X
    extract : M X → X

--The above extract is bullshit in general, it is just to introduce a sequence of binds that is not normalised by Agda.

  mufft : ∀ {s} → Ar s ℂ → Ar s ℂ
  mufft {ι n} a = (DFT a)
  mufft {s ⊗ p} a =
    extract (do
      b ← return (reshape swap (mapLeft mufft a))
      c ← return (zipWith _*_ b twiddles′)
      d ← return (reshape swap  (mapLeft mufft (c)))
      return d)
  -}
  
  ufft-helper : Ar s ℂ → Ar s ℂ
  ufft-helper {ι x} a = DFT a
  ufft-helper {s ⊗ s₁} a = let
      b = mapLeft ufft-helper $ reshape swap a
      c = zipWith _*_ b pretwiddles
      d = mapLeft ufft-helper $ reshape swap c
    in d

  ufft : Ar s ℂ → Ar s ℂ
  ufft {s} a = reshape (♯ ∙ reindex (sym (|s|≡|sᵗ| {s})) ∙ ♭ ∙ recursive-transposeᵣ) (ufft-helper a)
  
  ufft′-helper : Ar s ℂ → Ar s ℂ
  ufft′-helper {ι x} a = DFT a
  ufft′-helper {s ⊗ s₁} a = let
      b = reshape swap $ mapLeft ufft′-helper a
      c = zipWith _*_ b pretwiddles′
      d = reshape swap $ mapLeft ufft′-helper c
    in d

  ufft′ : Ar s ℂ → Ar s ℂ
  ufft′ {s} a = ufft-helper (reshape (♯ ∙ reindex (sym (|s|≡|sᵗ| {s})) ∙ ♭ ∙ recursive-transposeᵣ) a)

  
  nz≡nzₛ : ∀ {n : ℕ} → ∀ (nz-n : NonZero n) → ∀ (nzₛ-n : NonZeroₛ (ι n)) → (ι nz-n) ≡ nzₛ-n
  nz≡nzₛ {suc n} nz-n (ι x) = refl
  
  {-
  lemma₁ : ∀ {a : Ar s ℂ} → ufft  a ≅ (reshape (♯ ∙ reindex (sym (|s|≡|sᵗ| {s})) ∙ ♭) $ FFT a)
  lemma₁ {(ι n)} {a} (ι x) with nonZero? n | nonZeroDec (ι n)
  ... | no ¬a | no ¬a₁ = refl
  ... | no ¬nz-n | yes (ι nz-n) = ⊥-elim (¬nz-n nz-n)
  ... | yes nz-n | no ¬nz-n = ⊥-elim (¬nz-n (ι nz-n))
  ... | yes nz-n | yes nzₛ-n = cong (λ nz → FFT′ {ι n} ⦃ nz ⦄ _ _) (nz≡nzₛ nz-n nzₛ-n )
  lemma₁ {s₁ ⊗ s₂} {a} (i₁ ⊗ i₂) with nonZeroDec (s₁ ⊗ s₂) 
  ... | no ¬a = ?
  ... | yes (nz-s₁ ⊗ nz-s₂) = ?

  lemma₂ : ∀ {a : Ar s ℂ} → ufft′ a ≅ (reshape (♯ ∙ reindex (sym (|s|≡|sᵗ| {s})) ∙ ♭) $ FFT a)
  lemma₂ {(ι n)} {a} (ι x) with nonZero? n | nonZeroDec (ι n)
  ... | no ¬a | no ¬a₁ = refl
  ... | no ¬nz-n | yes (ι nz-n) = ⊥-elim (¬nz-n nz-n)
  ... | yes nz-n | no ¬nz-n = ⊥-elim (¬nz-n (ι nz-n))
  ... | yes nz-n | yes nzₛ-n = cong (λ nz → FFT′ ⦃ nz ⦄ _ _) (nz≡nzₛ nz-n nzₛ-n )
  lemma₂ {.(_ ⊗ _)} {a} (i ⊗ i₁) = ?

  prf : ∀ {a : Ar s ℂ} → ufft a ≅ ufft′ a
  prf {ι x} {a} i = refl
  prf {s₁ ⊗ s₂} {a} (i₁ ⊗ i₂) = ?
    --begin 
    --_ ≡⟨ lemma₁ {s₁ ⊗ s₂} {a} (i₁ ⊗ i₂) ⟩
    --_ ≡⟨ sym (lemma₂ (i₁ ⊗ i₂)) ⟩
    --_ ∎
  -}
    
  {-
  --Pick arbitrary array, and normalise mufft application to it, you will see the right pattern.
  tmp : mufft {(ι 7 ) ⊗ (ι 3 ⊗ ι 5)} ≡ ?
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
  
  trans-copy : Ar (ι V ⊗ s) (Ar p ℂ) → Ar s (Ar p (Ar (ι V) ℂ))
  trans-copy xs ps pp p4 = xs (p4 ⊗ ps) pp
  
  copy-trans : Ar s (Ar p (Ar (ι V) ℂ)) → Ar (ι V ⊗ s) (Ar p ℂ)
  copy-trans xs (p4 ⊗ ps) pp = xs ps pp p4

  ufft-vec : Ar s (Ar (ι V) ℂ) → Ar s (Ar (ι V) ℂ)
  ufft-vec xs ps pv = ufft′ ((nest $ reshape swap $ unnest xs) pv) ps
  --ufft-vec xs ps pv = mufft ((nest $ reshape swap $ unnest xs) pv) ps
  
  --twid-vec : Position s₁ → Ar s₂ (Ar (ι V) ℂ) → Ar s₂ (Ar (ι V) ℂ)
  --twid-vec ps₁ xs ps₂ pv = _*_ (xs ps₂ pv) (twiddles′ ?)
  --
  --
  --twid-vec′ : SIMD (s ⊗ p) → ?

  offt : ∀ {s} → SIMD s → Ar s ℂ → Ar s ℂ

  mapVec : SIMD (s ⊗ p) → Ar (s ⊗ p) ℂ → Ar (s ⊗ p) ℂ
  mapVec ι a = let
                  t = (nest ∘ reshape swap) a
                  w = ufft-vec t
                  q = (reshape swap ∘ unnest) w
                in q
  mapVec (p ⊗ ι) a = let
                        t = trans-copy (reshape (comp-resh p) (nest a))
                        w = Matrix.map ufft-vec t
                        --x , y = rem p
                        --a = Matrix.imap (?) w
                        q = reshape (rev (comp-resh p)) (copy-trans w)
                     in Matrix.unnest q
  mapVec (p ⊗ s@(s₁ ⊗ s₂)) a = mapLeft (offt s) a

  offt (ι ) a = reshape ♯ (DFT (reshape ♭ a)) -- non-vectorised fft, whatever it is
  offt (s ⊗ p) a = let
      b = (reshape swap (mapVec (s ⊗ p) a))
      c = (zipWith _*_ b twiddles′)
      d = (reshape swap  (mapVec (p ⊗ s) c))
      in d
  --offt (s ⊗ p) a =
  --  extract (do
  --    b ← return (reshape swap (mapVec (s ⊗ p) a))
  --    c ← return (zipWith _*_ b twiddles′)
  --    d ← return (reshape swap  (mapVec (p ⊗ s) c))
  --    return d)






