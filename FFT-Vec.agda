
open import Real using (Real)
open import Complex using (Cplx)

import Algebra.Structures as AlgebraStructures

import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning



module FFT-Vec (cplx : Cplx) where
  open Cplx cplx

  open AlgebraStructures  {A = ℂ} _≡_
  open IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid) renaming (*-comm to 𝕔*-comm)

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

  reshape-cong : ∀ {xs ys : Ar s ℂ} → (r : Reshape s p) → xs ≅ ys → reshape r xs ≅ reshape r ys
  reshape-cong {xs} {ys} r prf i = ?

  reshape-cong′ : ∀ {xs : Ar s ℂ} → {r₁ r₂ : Reshape s p} → r₁ ≡ r₂ → reshape r₁ xs ≅ reshape r₂ xs

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

  --------------------------
  ---- UFFT definitions ----
  --------------------------

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

  -- Proofs on ufft and ufft′

  ufft≅fft : ∀ {a : Ar s ℂ} → ufft  a ≅ (reshape (♯ ∙ reindex (sym (|s|≡|sᵗ| {s})) ∙ ♭) $ FFT a)
  ufft≅fft {(ι n)} {a} (ι x) with nonZero? n | nonZeroDec (ι n)
  ... | no ¬a | no ¬a₁ = refl
  ... | no ¬nz-n | yes (ι nz-n) = ⊥-elim (¬nz-n nz-n)
  ... | yes nz-n | no ¬nz-n = ⊥-elim (¬nz-n (ι nz-n))
  ... | yes nz-n | yes nzₛ-n = cong (λ nz → FFT′ {ι n} ⦃ nz ⦄ _ _) (nz≡nzₛ nz-n nzₛ-n )
  ufft≅fft {s₁ ⊗ s₂} {a} (i₁ ⊗ i₂) with nonZeroDec (s₁ ⊗ s₂) 
  ... | no ¬a = ?
  ... | yes (nz-s₁ ⊗ nz-s₂) = ?

  ufft′≅fft : ∀ {a : Ar s ℂ} → ufft′ a ≅ (reshape (♯ ∙ reindex (sym (|s|≡|sᵗ| {s})) ∙ ♭) $ FFT a)
  ufft′≅fft {(ι n)} {a} (ι x) with nonZero? n | nonZeroDec (ι n)
  ... | no ¬a | no ¬a₁ = refl
  ... | no ¬nz-n | yes (ι nz-n) = ⊥-elim (¬nz-n nz-n)
  ... | yes nz-n | no ¬nz-n = ⊥-elim (¬nz-n (ι nz-n))
  ... | yes nz-n | yes nzₛ-n = ? --cong (λ nz → FFT′ {?} ⦃ nz ⦄ _ _) (nz≡nzₛ nz-n nzₛ-n )
  ufft′≅fft {.(_ ⊗ _)} {a} (i ⊗ i₁) = ?

  ufft≅ufft′ : ∀ {a : Ar s ℂ} → ufft a ≅ ufft′ a
  ufft≅ufft′ {ι x} {a} i = ?
  ufft≅ufft′ {s₁ ⊗ s₂} {a} (i₁ ⊗ i₂) = ?

  ufft-helper-cong : ∀ {s : Shape} {xs ys : Ar s ℂ} → xs ≅ ys → ufft-helper xs ≅ ufft-helper ys
  -------------------------------------
  ---- UFFT with embedded twiddles ----
  -------------------------------------

  ufftₑ-helper : Ar s ℂ → Ar s ℂ
  ufftₑ-helper {ι x} a = DFT a
  ufftₑ-helper {s₁ ⊗ s₂} a = let
      b = unnest ∘ imap (λ i → zipWith _*_ ((nest $ pretwiddles {s₂} {s₁}) i) ∘ ufftₑ-helper) ∘ nest $ reshape swap a
      d = mapLeft ufftₑ-helper $ reshape swap b
    in d

  ufftₑ : Ar s ℂ → Ar s ℂ
  ufftₑ {s} a = reshape (♯ ∙ reindex (sym (|s|≡|sᵗ| {s})) ∙ ♭ ∙ recursive-transposeᵣ) (ufftₑ-helper a)

  ufftₑ-helper-cong : ∀ {s : Shape} {xs ys : Ar s ℂ} → xs ≅ ys → ufftₑ-helper xs ≅ ufftₑ-helper ys
  
  ufftₑ-helper≅ufft-helper : ∀ (a : Ar s ℂ) → ufftₑ-helper a ≅ ufft-helper a
  ufftₑ-helper≅ufft-helper {ι x} a i = refl
  ufftₑ-helper≅ufft-helper {s₁ ⊗ s₂} a (i₁ ⊗ i₂) = 
      begin 
      _ ≡⟨ ufftₑ-helper-cong (λ i → 𝕔*-comm _ _) i₂ ⟩
      _ ≡⟨ ufftₑ-helper≅ufft-helper _ i₂ ⟩
      _ ≡⟨ ufft-helper-cong (λ i → cong₂ _*_ (ufftₑ-helper≅ufft-helper _ i₁ ) refl) (i₂)  ⟩
      _ ∎

  ufftₑ≅ufft : ∀ (a : Ar s ℂ) → ufftₑ a ≅ ufft a
  ufftₑ≅ufft {s} a i = reshape-cong 
        (♯ ∙ reindex (sym (|s|≡|sᵗ| {s})) ∙ ♭ ∙ recursive-transposeᵣ)
        (ufftₑ-helper≅ufft-helper a)
        i
  
  -------------------------
  ---- SIMD Guided FFT ----
  -------------------------

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
                  b = map ufftₑ a 
                  c = nest (reshape swap (unnest b))
                in c

  -- SIMD Guided reshape

  -- This implementation could end up being a nightmare when it comes to proof, rewrite in a nicer way (with the same effect)
  --SIMD-transpose′ : ∀ {s : Shape} → SIMD s → ∃ λ p → (Reshape s p × length s ≡ length p)
  --SIMD-transpose′ {(ι V ⊗ s)} ι = (ι V ⊗ s) , (eq , refl) --(s ⊗ ι V) , (swap , |s|≡|sᵗ| {ι V ⊗ ι (length s)})
  --SIMD-transpose′ {(s₁ ⊗ s₂) ⊗ s₃} (simd₁ ⊗ simd₂) with SIMD-transpose′ simd₁ | SIMD-transpose′ simd₂
  --... | s₁′ , (rshp₁ , prf₁) | s₂′ , (rshp₂ , prf₂) = 
  --        s₂′ ⊗ s₁′ 
  --      , (swap ∙ rshp₁ ⊕ rshp₂ 
  --      , trans (cong₂ _*ₙ_ prf₁ prf₂) (*-comm (length s₁′) (length s₂′)) )

  SIMD-transpose : SIMD s → Shape
  SIMD-transpose {ι x} ()
  SIMD-transpose {.(ι V) ⊗ s} ι = ι V ⊗ s
  SIMD-transpose (simd-s₁ ⊗ simd-s₂) = (SIMD-transpose simd-s₂) ⊗ (SIMD-transpose simd-s₁)
  
  SIMD-transposeᵣ : (simd-s : SIMD s) → Reshape s (SIMD-transpose simd-s)
  SIMD-transposeᵣ ι = eq
  SIMD-transposeᵣ (simd-s ⊗ simd-s₁) = swap ∙ SIMD-transposeᵣ simd-s ⊕ SIMD-transposeᵣ simd-s₁

  SIMD-transposeₗ : (simd-s : SIMD s) → length (SIMD-transpose simd-s) ≡ length s
  SIMD-transposeₗ ι = refl
  SIMD-transposeₗ {(s₁ ⊗ s₂)} (simd-s₁ ⊗ simd-s₂) = 
        trans 
          (cong₂ _*ₙ_ (SIMD-transposeₗ simd-s₂) (SIMD-transposeₗ simd-s₁))
          (*-comm (length (s₂)) (length (s₁)))

  SIMD-transpose-reindex : SIMD s → Reshape s s
  SIMD-transpose-reindex simd-s = ♯ ∙ reindex (SIMD-transposeₗ simd-s) ∙ ♭ ∙ (SIMD-transposeᵣ simd-s)
  
  -- SIMD Guided twiddles
  SIMD-preoffset-prod : SIMD p → Position (s ⊗ p) → ℕ
  SIMD-preoffset-prod simd-p (k ⊗ j) = iota (k ⟨ ♯ ⟩) *ₙ iota (j ⟨ rev (SIMD-transposeᵣ simd-p) ∙ ♯ ⟩)

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
                  z = imap (λ i → zipWith _*_ (nest pretwiddles i)) w
                  q = (reshape swap ∘ unnest) z
                  --p = zipWith _*_ q pretwiddles
                in q
  mapVec′ (simd-s ⊗ ι) false a = let
                  t = trans-copy (reshape (comp-resh simd-s) (nest a))
                  w = Matrix.map ufft-vec t
                  q = reshape (rev (comp-resh simd-s)) (copy-trans w)
               in Matrix.unnest q
               -- TODO: Confirm following line is correct
  mapVec′ (_ ⊗ simd-p@(_ ⊗ _)) false = mapLeft (offt simd-p)
  mapVec′ {s₁ ⊗ s₂} {.(ι V ⊗ s)} (simd-s ⊗ ι {s}) true a = let
                      t = trans-copy (reshape (comp-resh simd-s) (nest a))
                      w = Matrix.map ufft-vec t
                      twids  = SIMD-pretwiddles {s₁ ⊗ s₂} {ι V ⊗ s} ι
                      x = imap {s₁ ⊗ s₂} (λ i → zipWith _*_ 
                                        ((copy-trans w) (i ⟨ (rev (comp-resh simd-s)) ⟩ )) 
                                        (nest twids i)
                                )
                      y = unnest (reshape (rev (comp-resh simd-s)) (copy-trans w))
                   in y 
  -- TODO: Below line is not hit with current tests so may be incorrect, need to do proof as too many dimensions to compile (4*3*3 min to avoid symmetry)
  mapVec′ (_ ⊗ simd-p@(_ ⊗ _)) true a = let
                                    w = mapLeft (offt simd-p) a
                                    x = zipWith _*_ w (SIMD-pretwiddles simd-p)
                                  in x

  offt (ι ) a = ufftₑ a
  offt {s₁ ⊗ p₁} (s ⊗ p) a = let
      b = (mapVec′ (p ⊗ s) true  (reshape swap a))
      c = (mapVec′ (s ⊗ p) false (reshape swap b))
      in c
  
  -- Use of SIMD-transpose-reindex does however make the proof more annoying than
  -- recursive-transposeᵣ did, as although the shape is recursivly transposed and
  -- flattened in both cases, it does it in more steps... 
  nofft : ∀ {s} → SIMD s → Ar s ℂ → Ar s ℂ
  nofft {s} simd a = reshape (SIMD-transpose-reindex simd) (offt simd a)

  offt-cong : ∀ {s : Shape} {xs ys : Ar s ℂ} → (simd-s : SIMD s) → xs ≅ ys → offt simd-s xs ≅ offt simd-s ys

  lemma₁ : ∀ {s : Shape} → (SIMD s) → 
        (eq ⊕ rev ♭ ∙ split ∙ subst (λ t → Reshape (ι (length (recursive-transpose s) *ₙ 4)) (ι t)) (sym (|s|≡|sᵗ| {ι V ⊗ s})) eq ∙ (flat {length $ recursive-transpose s}) ∙ ♭ ⊕ eq ∙ swap ∙ (_⊕_ {ι V} {ι V} {s} eq  recursive-transposeᵣ)) 
      ≡ (eq ⊕ rev ♭ ∙ split {V} {length s} ∙ flat {V} {length  s} ∙ _⊕_ {ι V} {ι V} {s} eq ♭ ∙ eq ⊕ rev ♭ ∙ split ∙ subst (λ t → Reshape (ι (length (recursive-transpose s) *ₙ 4)) (ι t)) (sym (|s|≡|sᵗ| {ι V ⊗ s})) eq ∙ flat ∙ ♭ ⊕ eq ∙ swap ∙ eq ⊕ recursive-transposeᵣ)
  lemma₁ {s} simd-s = ?

  ufftₑ⇒offt : (simd : SIMD s) → ∀ (a : Ar s ℂ) → ufftₑ a ≅ nofft simd a
  -- Current big hole - ?9 doesn't seem to be fillable without making a contradiction.........
  ufftₑ⇒offt {(ι V ⊗ s)} (ι {.(s)}) a i = (reshape-cong′ {?} {?} {?} {?} {?} (lemma₁ (ι {s}))) (?)
  {-
    begin 
      reshape (eq ⊕ rev ♭ ∙ split ∙ subst (λ t → Reshape (ι (length (recursive-transpose s) *ₙ 4)) (ι t)) (sym (|s|≡|sᵗ| {ι 4 ⊗ s})) eq ∙ (flat {length $ recursive-transpose s}) ∙ ♭ ⊕ eq ∙ swap ∙ (_⊕_ {ι 4} {ι 4} {s} eq recursive-transposeᵣ)) (unnest 
        (λ i₁ → ufftₑ-helper (λ j → (pretwiddles (j ⊗ i₁)) * (a (ι fzero ⊗ j) * -ω 4 0 + (a (ι (fsuc fzero) ⊗ j) * -ω 4 (iota i₁ +ₙ 0) + (a (ι (fsuc (fsuc fzero)) ⊗ j) * -ω 4 (iota i₁ +ₙ (iota i₁ +ₙ 0)) + (a (ι (fsuc (fsuc (fsuc fzero))) ⊗ j) * -ω 4 (iota i₁ +ₙ (iota i₁ +ₙ (iota i₁ +ₙ 0))) + 0ℂ))))))
       ) i
    ≡⟨ (reshape-cong′ {?} {?} {?} {?} {?} (lemma₁ (ι {?}))) i ⟩
      reshape (eq ⊕ rev ♭ ∙ split {V} {length s} ∙ flat {V} {length  s} ∙ _⊕_ {ι V} {ι V} {s} eq ♭ ∙ eq ⊕ rev ♭ ∙ split ∙ subst (λ t → Reshape (ι (length (recursive-transpose s) *ₙ 4)) (ι t)) (sym (|s|≡|sᵗ| {ι V ⊗ s})) eq ∙ flat ∙ ♭ ⊕ eq ∙ swap ∙ eq ⊕ recursive-transposeᵣ)
        (unnest
              (λ i₁ → ufftₑ-helper (λ j → (pretwiddles (j ⊗ i₁)) * (a (ι fzero ⊗ j) * -ω 4 0 + (a (ι (fsuc fzero) ⊗ j) * -ω 4 (iota i₁ +ₙ 0) + (a (ι (fsuc (fsuc fzero)) ⊗ j) * -ω 4 (iota i₁ +ₙ (iota i₁ +ₙ 0)) + (a (ι (fsuc (fsuc (fsuc fzero))) ⊗ j) * -ω 4 (iota i₁ +ₙ (iota i₁ +ₙ (iota i₁ +ₙ 0))) + 0ℂ))))))
         )   ( i )
      ∎
  -}


--         eq ⊕ rev ♭ ∙ split {V} {length s} ∙ flat {V} {length  s} ∙ _⊕_ {ι V} {ι V} {s} eq ♭ ∙ eq ⊕ rev ♭ ∙ split ∙ subst (λ t → Reshape (ι (length (recursive-transpose s) *ₙ 4)) (ι t)) (sym (|s|≡|sᵗ| {ι V ⊗ s})) eq ∙ flat ∙ ♭ ⊕ eq ∙ swap ∙ eq ⊕ recursive-transposeᵣ 


    --(((((((i ⟨ eq ⊕ rev ♭ ⟩) ⟨ split ⟩) ⟨ subst (λ t → Reshape (ι (length (recursive-transpose s) *ₙ 4)) (ι t)) (sym |s|≡|sᵗ|) eq ⟩) ⟨ flat ⟩) ⟨ ♭ ⊕ eq ⟩) ⟨ swap ⟩) ⟨ eq ⊕ recursive-transposeᵣ ⟩)
  ufftₑ⇒offt {.(_ ⊗ _)} (simd-s ⊗ simd-s₁) a i = ?
  {-
  --ufft-helper⇒offt-helper : (simd : SIMD s) → ∀ (a : Ar s ℂ) → ufft-helper a ≅ offt simd a
  lemma₁ : 
        (x : Fin V) 
      → (i₁ : Position s)
      →
      (((((((ι x ⊗ (i₁ ⟨ rev ♭ ⟩)) ⟨ split ⟩) ⟨ subst (λ t → Reshape (ι (length (recursive-transpose s) *ₙ 4)) (ι t)) (sym (|s|≡|sᵗ| {ι 4 ⊗ s})) eq ⟩) ⟨ flat {length (recursive-transpose s)} ⟩) ⟨ (♭ {recursive-transpose s}) ⊕ eq ⟩) ⟨ swap ⟩) ⟨ eq ⊕ recursive-transposeᵣ ⟩)
      ≡
      (((((((((((ι x ⊗ (i₁ ⟨ rev ♭ ⟩)) ⟨ split ⟩) ⟨ flat {?} ⟩) ⟨ eq ⊕ ♭ ⟩) ⟨ eq ⊕ rev ♭ ⟩) ⟨ split ⟩) ⟨ subst (λ t → Reshape (ι (length (recursive-transpose s) *ₙ 4)) (ι t)) (sym (|s|≡|sᵗ| {ι V ⊗ s})) eq ⟩) ⟨ flat ⟩) ⟨ ♭ ⊕ eq ⟩) ⟨ swap ⟩) ⟨ eq ⊕ recursive-transposeᵣ ⟩)

  ufft⇒offt : (simd : SIMD s) → ∀ (a : Ar s ℂ) → ufft a ≅ nofft simd a
  ufft⇒offt {ι .V ⊗ s} ι a (ι x ⊗ i₁) =
      unnest
            (λ i →
               ufft-helper
               (λ j →
                  (a (ι fzero ⊗ j) * -ω 4 0 +
                   (a (ι (fsuc fzero) ⊗ j) * -ω 4 (iota i +ₙ 0) +
                    (a (ι (fsuc (fsuc fzero)) ⊗ j) * -ω 4 (iota i +ₙ (iota i +ₙ 0)) +
                     (a (ι (fsuc (fsuc (fsuc fzero))) ⊗ j) *
                      -ω 4 (iota i +ₙ (iota i +ₙ (iota i +ₙ 0)))
                      + 0ℂ))))
                  *
                  (pretwiddles (j ⊗ i))))
            (((((((ι x ⊗ (i₁ ⟨ rev ♭ ⟩)) ⟨ split ⟩) ⟨
                 subst
                 (λ t → Reshape (ι (length (recursive-transpose s) *ₙ 4)) (ι t))
                 (sym (|s|≡|sᵗ| {ι 4 ⊗ s})) eq
                 ⟩)
                ⟨ flat ⟩)
               ⟨ ♭ ⊕ eq ⟩)
              ⟨ swap ⟩)
             ⟨ eq ⊕ recursive-transposeᵣ ⟩)
      ≡⟨ cong (unnest (λ i → ufft-helper (λ j → (a (ι fzero ⊗ j) * -ω 4 0 + (a (ι (fsuc fzero) ⊗ j) * -ω 4 (iota i +ₙ 0) + (a (ι (fsuc (fsuc fzero)) ⊗ j) * -ω 4 (iota i +ₙ (iota i +ₙ 0)) + (a (ι (fsuc (fsuc (fsuc fzero))) ⊗ j) * -ω 4 (iota i +ₙ (iota i +ₙ (iota i +ₙ 0))) + 0ℂ)))) * (pretwiddles (j ⊗ i))))) ? ⟩
        unnest
            (λ i →
               ufft-helper
               (λ j →
                  (a (ι fzero ⊗ j) * -ω 4 0 +
                   (a (ι (fsuc fzero) ⊗ j) * -ω 4 (iota i +ₙ 0) +
                    (a (ι (fsuc (fsuc fzero)) ⊗ j) * -ω 4 (iota i +ₙ (iota i +ₙ 0)) +
                     (a (ι (fsuc (fsuc (fsuc fzero))) ⊗ j) *
                      -ω 4 (iota i +ₙ (iota i +ₙ (iota i +ₙ 0)))
                      + 0ℂ))))
                  *
                  (pretwiddles (j ⊗ i))))
            (((((((((((ι x ⊗ (i₁ ⟨ rev ♭ ⟩)) ⟨ split ⟩) ⟨ flat {?} ⟩) ⟨ eq ⊕ ♭ ⟩) ⟨
                   eq ⊕ rev ♭ ⟩)
                  ⟨ split ⟩)
                 ⟨
                 subst
                 (λ t → Reshape (ι (length (recursive-transpose s) *ₙ 4)) (ι t))
                 (sym (|s|≡|sᵗ| {ι V ⊗ s})) eq
                 ⟩)
                ⟨ flat ⟩)
               ⟨ ♭ ⊕ eq ⟩)
              ⟨ swap ⟩)
             ⟨ eq ⊕ recursive-transposeᵣ ⟩)
      ∎
  ufft⇒offt {.(_ ⊗ _)} (simd ⊗ simd₁) a i = ?
  -}

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






