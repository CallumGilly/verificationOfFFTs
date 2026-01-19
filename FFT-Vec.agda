
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
  open import Data.Bool


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

  --ufft′′ : Ar s ℂ → Ar s ℂ
  --ufft′′ {s} a = ufft-helper (reshape (♯ ∙ reindex (sym (|s|≡|sᵗ| {s})) ∙ ♭ ) a)

  
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
  ufft-vec xs = let
                  a = nest (reshape swap (unnest xs))
                  b = map ufft a 
                  c = nest (reshape swap (unnest b))
                in c

  -- SIMD Guided reshape

  -- This implementation could end up being a nightmare when it comes to proof, rewrite in a nicer way (with the same effect)
  SIMD-transpose : ∀ {s : Shape} → SIMD s → ∃ λ p → (Reshape s p × length s ≡ length p)
  SIMD-transpose {(ι V ⊗ s)} ι = (ι V ⊗ s) , (eq , refl) --(s ⊗ ι V) , (swap , |s|≡|sᵗ| {ι V ⊗ ι (length s)})
  SIMD-transpose {(s₁ ⊗ s₂) ⊗ s₃} (simd₁ ⊗ simd₂) with SIMD-transpose simd₁ | SIMD-transpose simd₂
  ... | s₁′ , (rshp₁ , prf₁) | s₂′ , (rshp₂ , prf₂) = 
          s₂′ ⊗ s₁′ 
        , (swap ∙ rshp₁ ⊕ rshp₂ 
        , trans (cong₂ _*ₙ_ prf₁ prf₂) (*-comm (length s₁′) (length s₂′)) )

  SIMD-transpose-reindex : SIMD s → Reshape s s
  SIMD-transpose-reindex simd with SIMD-transpose simd
  ... | s′ , (rshp , prf) = ♯ ∙ reindex (sym prf) ∙ ♭ ∙ rshp
  
  -- SIMD Guided twiddles
  SIMD-preoffset-prod : SIMD p → Position (s ⊗ p) → ℕ
  SIMD-preoffset-prod simd-p (k ⊗ j) = iota (k ⟨ ♯ ⟩) *ₙ iota (j ⟨ rev (SIMD-transpose simd-p .proj₂ .proj₁) ∙ ♯ ⟩)

  SIMD-pretwiddles : ∀ {s p : Shape} → SIMD p → Ar (s ⊗ p) ℂ
  SIMD-pretwiddles {s} {p} simd-p i with nonZeroDec (s ⊗ p)
  ... | no ¬nz = ⊥-elim (zs-nopos ¬nz i)
  ... | yes nz = -ω (length (s ⊗ p)) ⦃ nonZeroₛ-s⇒nonZero-s nz ⦄ (SIMD-preoffset-prod simd-p i)


  offt : ∀ {s} → SIMD s → Ar s ℂ → Ar s ℂ

  mapVec′ : SIMD (s ⊗ p) → (twiddle : Bool) → Ar (s ⊗ p) ℂ → Ar (s ⊗ p) ℂ
  mapVec′ ι false a = let
                  t = (nest ∘ reshape swap) a
                  w = ufft-vec t
                  q = (reshape swap ∘ unnest) w
                in q
  mapVec′ ι true  a = let
                  t = (nest ∘ reshape swap) a
                  w = ufft-vec t
                  q = (reshape swap ∘ unnest) w
                  p = zipWith _*_ q pretwiddles
                in p
  mapVec′ (simd-s ⊗ ι) false a = let
                  t = trans-copy (reshape (comp-resh simd-s) (nest a))
                  w = Matrix.map ufft-vec t
                  q = reshape (rev (comp-resh simd-s)) (copy-trans w)
               in Matrix.unnest q
               -- TODO: Confirm following line is correct
  mapVec′ (simd-s ⊗ s@(simd-p ⊗ simd-p₁)) false = mapLeft (offt s)
  mapVec′ (simd-s ⊗ ι {s₁}) true a = let
                        t = trans-copy (reshape (comp-resh simd-s) (nest a))
                        w = Matrix.map ufft-vec t
                        x = zipWith _*_ (unnest (reshape (rev (comp-resh simd-s)) (copy-trans w))) (SIMD-pretwiddles ι)
                     in x 
  -- TODO: Below line is not hit with current tests so may be incorrect, need to do proof as too many dimensions to compile (4*3*3 min to avoid symmetry), also need to consider need for twid
  -- id used to make it clear this is skipped as will produce massive error
  mapVec′ (simd-s ⊗ (simd-p ⊗ simd-p₁)) true a = id a -- TODO
                                  --let
                                  --  w = mapLeft (offt s) a
                                  --  --x = zipWith _*_ w pretwiddles
                                  --  x = zipWith _*_ w (SIMD-pretwiddles (s₁ ⊗ s₂))
                                  --in x

  offt (ι ) a = ufft-helper a
  offt {s₁ ⊗ p₁} (s ⊗ p) a = let
      b = (mapVec′ (p ⊗ s) true  (reshape swap a))
      c = (mapVec′ (s ⊗ p) false (reshape swap b))
      in c
  
  -- Use of SIMD-transpose-reindex does however make the proof more annoying than
  -- recursive-transposeᵣ did, as although the shape is recursivly transposed and
  -- flattened in both cases, it does it in more steps... 
  nofft : ∀ {s} → SIMD s → Ar s ℂ → Ar s ℂ
  nofft {s} simd a = reshape (SIMD-transpose-reindex simd) (offt simd a)

  _ : mapLeft ufft′-helper ≡ ?
  _ = ?

  reshape-cong : ∀ {xs ys : Ar s ℂ} → (r : Reshape s p) → xs ≅ ys → reshape r xs ≅ reshape r ys
  reshape-cong {xs} {ys} r prf i = ?

  ufft-helper⇒offt-helper : (simd : SIMD s) → ∀ (a : Ar s ℂ) → ufft-helper a ≅ offt simd a
  ufft-helper⇒offt-helper ι a i = refl
  ufft-helper⇒offt-helper {.((ι V ⊗ _) ⊗ (_ ⊗ _))} (ι ⊗ simd₁) a ((i₁ ⊗ i₂) ⊗ (i₃ ⊗ i₄)) = ?
  ufft-helper⇒offt-helper {.((_ ⊗ _) ⊗ (_ ⊗ _))} ((simd ⊗ simd₂) ⊗ simd₁) a ((i₁ ⊗ i₂) ⊗ (i₃ ⊗ i₄)) = ?

  ufft⇒offt : (simd : SIMD s) → ∀ (a : Ar s ℂ) → ufft a ≅ nofft simd a
  ufft⇒offt {s} simd a i =
    --(reshape-cong
    --  {s}
    --  {_} 
    --  {ufft-helper a}
    --  {offt simd a}
    --  (?)
    --  (λ j → ufft-helper⇒offt-helper simd a j)
    --) i

  --cong (_ (i ⟨ ♯ ∙ reindex (sym (|s|≡|sᵗ| {s})) ∙ ♭ ∙ recursive-transposeᵣ ⟩ )) ?

  --ufft′ {s} a = ufft-helper (reshape (♯ ∙ reindex (sym (|s|≡|sᵗ| {s})) ∙ ♭ ∙ recursive-transposeᵣ) a)
  

  --offt (s ⊗ p) a =
  --  extract (do
  --    b ← return (reshape swap (mapVec (s ⊗ p) a))
  --    c ← return (zipWith _*_ b twiddles′)
  --    d ← return (reshape swap  (mapVec (p ⊗ s) c))
  --    return d)






