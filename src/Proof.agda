open import src.Real using (Real)
module src.Proof (r : Real) where
open import Data.Nat.Base using (ℕ; suc; zero) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties using (*-zeroʳ; *-comm; _≟_)
open import Data.Fin.Base using (Fin; quotRem; toℕ; combine; remQuot; quotient; remainder; cast) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (cast-is-id)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)

open import src.Matrix using (Ar; Shape; _⊗_; ι; _==_; Position; nestedMap; zipWith; nest; map; unnest; head₁; tail₁; zip; iterate; ι-cons; nil; foldr; length; cong-foldr)
open import src.Reshape using (reshape; Reshape; flat; _♭; _♯; recursive-transpose; recursive-transposeᵣ; _∙_; rev; _⊕_; swap; eq; split; _⟨_⟩; eq+eq; _♭₂; comm-eq)
open import src.Complex r using (ℂ; _*_; _+_; ℂfromℕ; -ω; +-identityʳ; ω-N-0; *-identityʳ; _+_i)
open ℂ using (real; imaginary)
open import src.FFT r using (FFT; twiddles; position-sum; offset-n)
open import src.DFTMatrix r using (DFT; posVec; step)
open import src.Extensionality using (extensionality)
open import Relation.Nullary using (Dec; yes; no)
open Real r using (ℝ; π; sin; cos; double-negative; _ᵣ; -ᵣ-identityʳ; *ᵣ-zeroᵣ; +ᵣ-identityˡ; *ᵣ-identityʳ; /ᵣ-zeroₜ; +ᵣ-identityʳ; +ᵣ-assoc; +ᵣ-comm)
  renaming (_+_ to _+ᵣ_; _-_ to _-ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_)

open import Function.Base using (_$_; id; _∘_; flip; _∘₂_)

open import src.MatrixEquality as MatEq
open MatEq using (_≅_; mat-refl)
open MatEq.≅-Reasoning


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; subst; cong-app)
open Eq.≡-Reasoning

-- This allows for pattern matching on the inside of zipWith
lemma₂ : ∀ {n : ℕ} {arr : Ar (ι n) ℂ} → (λ p → arr p) ≡ λ{(ι x) → arr (ι x)}
lemma₂ {n} {arr} = extensionality λ{(ι x) → refl}

DFT≡DFT : ∀ {n : ℕ} (arr₁ arr₂ : Ar (ι n) ℂ) → arr₁ ≅ arr₂ → DFT arr₁ ≅ DFT arr₂
DFT≡DFT arr₁ .arr₁ (mat-refl {i} x) = mat-refl {i = i} refl

--FFT≅FFT : ∀ {s : Shape} {arr₁ arr₂ : Ar s ℂ} → ?

theorm-new : ∀ {s : Shape} {arr : Ar s ℂ} {i : Position (recursive-transpose s)}
  → FFT arr ≅ ((reshape _♯) ∘ DFT ∘ (reshape {s} _♭₂)) arr
theorm-new {ι n} {arr} {i} = mat-refl {i = i} refl
theorm-new {s ⊗ s₁} {arr} {i} =
  ≅-begin
    FFT arr
  ≅⟨⟩
    ?

theorm₅ : ∀ {n m : ℕ}
  → FFT ≡ (reshape _♯) ∘ DFT ∘ (reshape {ι n ⊗ ι m} _♭₂)
theorm₅ {n} {m} = 
  extensionality λ{ arr →
    extensionality λ{ (ι x ⊗ ι y) →
      begin
        FFT arr (ι x ⊗ ι y)
      ≡⟨⟩
        ( nest (
          reshape swap (nestedMap (DFT) (zipWith _*_ (reshape swap (nestedMap DFT (reshape swap arr))) twiddles))
        )) (ι x) (ι y)
      ≡⟨⟩
        (map 
           DFT
          (nest (zipWith _*_ (reshape swap (nestedMap DFT (reshape swap arr))) twiddles))
        ) (ι y) (ι x)
      ≡⟨⟩
        (DFT
          (
            zipWith _*_ 
              (
                (nest (reshape swap (unnest (map DFT (nest (reshape swap arr))))))
                (ι y)
              )
              ((nest twiddles) (ι y))
          )
        ) (ι x)
      ≡⟨⟩
        foldr 
          _+_ 
          (ℂfromℕ 0) 
          (zipWith 
            (step {m} {x})
            (zipWith 
              _*_ 
              (
                (λ (p) → DFT ((nest (reshape swap arr)) p) (ι y))
              )
              (nest twiddles (ι y))
            )
            posVec
          )
      ≡⟨⟩
        foldr 
          _+_ 
          (ℂfromℕ 0) 
          (zipWith 
            (step {m} {x})
            (zipWith 
              _*_ 
              (λ p → 
                foldr 
                  _+_ 
                  (ℂfromℕ 0)
                  (zipWith 
                    (step {n} {y})
                    (λ q → arr (q ⊗ p))
                    (posVec {n})
                  )
              )
              (nest twiddles (ι y))
            )
            (posVec {m})
          )
      ≡⟨⟩
        foldr 
          _+_ 
          (ℂfromℕ 0) 
          (λ p₀ → 
            step {m} {x}
              (
                (
                  foldr 
                    _+_ 
                    (ℂfromℕ 0)
                    (λ p₁ → step {n} {y} (arr (p₁ ⊗ p₀)) (posVec {n} p₁))
                )
                * 
                (twiddles (ι y ⊗ p₀))
              )
            (posVec {m} p₀)
          )
      ≡⟨⟩
        foldr 
          _+_ 
          (ℂfromℕ 0) 
          (λ p₀ → 
            step {m} {x}
              (
                (
                  foldr 
                    _+_ 
                    (ℂfromℕ 0)
                    (λ p₁ → step {n} {y} (arr (p₁ ⊗ p₀)) (posVec {n} p₁))
                )
                * 
                (twiddles (ι y ⊗ p₀))
              )
            (posVec {m} p₀)
          )
      ≡⟨ sym (flipped-thm n m arr x y) ⟩
        (reshape _♯ ∘
             DFT ∘ reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq))
            arr (ι x ⊗ ι y)
      ∎

    }
  }
  where
    flipped-thm : ∀ 
        (n   : ℕ)
        (m   : ℕ)
        (arr : Ar (ι n ⊗ ι m) ℂ)
        (x   : Fin m)
        (y   : Fin n)
      → 
        (reshape _♯ ∘ DFT ∘ reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq)) arr (ι x ⊗ ι y)
      ≡
        foldr _+_ (ℂfromℕ 0) (λ p₀ → step {m} {x} (foldr _+_ (ℂfromℕ 0) (λ p₁ → step {n} {y} (arr (p₁ ⊗ p₀)) (posVec p₁)) * twiddles (ι y ⊗ p₀)) (posVec p₀)) 
    flipped-thm n m arr x y = 
      begin
        (reshape _♯ ∘ DFT ∘ reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq)) arr (ι x ⊗ ι y)
      ≡⟨⟩
        (( DFT ( reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq) arr))) ((ι x ⊗ ι y) ⟨ rev _♭ ⟩ )
      ≡⟨⟩
        (( DFT ( reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq) arr))) ((ι x ⊗ ι y) ⟨ rev (flat ∙ _♭ ⊕ _♭) ⟩ )
      ≡⟨⟩
        (( DFT ( reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq) arr))) ((ι x ⊗ ι y) ⟨ (split) ⟩ )
      ≡⟨⟩
        (( DFT ( reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq) arr))) (ι (combine x y))
      ≡⟨⟩
        foldr _+_ (ℂfromℕ 0)
            (zipWith 
              step
              (reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq) arr)
              posVec
            )
      ≡⟨⟩
        foldr {m *ₙ n} _+_ (ℂfromℕ 0)
            (λ p₀ → 
              step {m *ₙ n}
              (reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq) arr p₀)
              (posVec p₀)
            )
--      ≡⟨ cong (foldr {m *ₙ n} _+_ (ℂfromℕ 0)) lemma₂ ⟩
--        foldr {m *ₙ n} _+_ (ℂfromℕ 0)
--            (λ{ (ι x) →
--              step {m *ₙ n} {x}
--              (reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq) arr (ι x))
--              (posVec (ι x))
--            })
        
      --≡⟨ cong (λ f → foldr {m *ₙ n} _+_ (ℂfromℕ 0) f) (lemma₂ {?} {?}) ⟩
      --  foldr {m *ₙ n} _+_ (ℂfromℕ 0)
      --      (λ{ (ι x) → 
      --        step {m *ₙ n} 
      --        (reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq) arr (ι x))
      --        (posVec (ι x))
      --      })
      ≡⟨⟩
        ?

theorm₄ : ∀ {s : Shape}
  → FFT ≡ (reshape _♯) ∘ DFT ∘ (reshape {s} _♭₂)
theorm₄ {ι x} = refl
theorm₄ {s ⊗ s₁} =
  extensionality λ{ arr →
    extensionality λ{ (p ⊗ p₁) →
      begin
        FFT arr (p ⊗ p₁)
      ≡⟨⟩
        reshape 
          swap 
          (nestedMap 
            FFT 
            (zipWith 
              _*_ 
              (reshape 
                swap 
                (nestedMap FFT (reshape swap arr))
              )
              twiddles
            )
          )
        (p ⊗ p₁)
      ≡⟨ cong (λ f → reshape swap (nestedMap f (zipWith _*_ (reshape swap (nestedMap FFT (reshape swap arr))) twiddles)) (p ⊗ p₁)) (theorm₄ {s₁}) ⟩
        reshape 
          swap 
          (nestedMap 
            ((reshape _♯) ∘ DFT ∘ (reshape {s₁} _♭₂)) 
            (zipWith 
              _*_ 
              (reshape 
                swap 
                (nestedMap FFT (reshape swap arr))
              )
              twiddles
            )
          )
        (p ⊗ p₁)
        
      ≡⟨ cong (λ f → reshape swap (nestedMap ((reshape _♯) ∘ DFT ∘ (reshape {s₁} _♭₂)) (zipWith _*_ (reshape swap (nestedMap f (reshape swap arr))) twiddles)) (p ⊗ p₁)) (theorm₄ {s}) ⟩
        reshape 
          swap 
          (nestedMap 
            (
                (reshape _♯)
              ∘ DFT 
              ∘ (reshape {s₁} _♭₂)
            ) 
            (zipWith 
              _*_ 
              (reshape 
                swap 
                (nestedMap 
                  ((reshape _♯) ∘ DFT ∘ (reshape {s} _♭₂)) 
                  (reshape swap arr)
                )
              )
              twiddles
            )
          )
        (p ⊗ p₁)
      ≡⟨⟩
        (
          (
            (
                (reshape {ι (length (recursive-transpose s₁))} {recursive-transpose s₁} _♯)
              ∘ DFT 
              ∘ (reshape {s₁} _♭₂)
            )
            ((nest 
              (zipWith 
                _*_ 
                (reshape 
                  swap 
                  (nestedMap 
                    ((reshape _♯) ∘ DFT ∘ (reshape {s} _♭₂)) 
                    (reshape swap arr)
                  )
                )
                twiddles
              )
            ) p₁)
          )
        )
        p
      ≡⟨⟩
        (
            (
                (reshape {ι (length (recursive-transpose s₁))} {recursive-transpose s₁} _♯)
              ∘ DFT 
              ∘ (reshape {s₁} _♭₂)
            )
            (
              (zipWith _*_ 
                ((nest
                  (reshape swap (nestedMap ((reshape _♯) ∘ DFT ∘ (reshape {s} _♭₂)) (reshape swap arr)))
                ) p₁)
                (( nest
                  twiddles
                ) p₁)
              )
            )
        )
        p
      ≡⟨⟩
        ?
    }
  }


--tmp : ∀ { s₁ s₂ : Shape} {arr₁ arr₂ : Ar (s₁ ⊗ s₂) ℂ} {p₁ : Position s₁} {p₂ : Position s₂} {f : ∀ {s : Shape} → Ar s ℂ → Ar s ℂ} → (f (nest arr₁ p₁)) p₂ ≡ ?

        
--lemma₁ : ∀ {s : Shape} → length s ≡ length (recursive-transpose s)
--lemma₁ {ι x}    = refl
--lemma₁ {s ⊗ s₁} rewrite 
--    *-comm (length s) (length s₁) 
--  | lemma₁ {s}
--  | lemma₁ {s₁} = refl
--
--lemma₂ : ∀ {s : Shape} → Position (ι (length s)) → Position (ι (length (recursive-transpose s)))
--lemma₂ {s} (ι x) = ι (cast (lemma₁ {s}) x)

--
----lemma₃ : ∀ {n m : ℕ} {x : Fin n} → {prf : n ≡ m} → cast {m} prf x ≡ x
----lemma₃ {n} = ?
--
--theorm : ∀ {s : Shape} (arr : Ar s ℂ)
--  → ((reshape _♭ ∘ FFT) arr) ∘ lemma₂ {s} ≡ (DFT ∘ (reshape {s} (_♭))) arr
--theorm {ι x} arr = 
--  extensionality λ{(ι p) →
--    begin
--      ((reshape eq ∘ FFT) arr ∘ lemma₂ {ι x}) (ι p)
--    ≡⟨⟩
--      FFT arr (lemma₂ {ι x} (ι p))
--    ≡⟨⟩
--      FFT arr (ι (cast refl p))
--    ≡⟨⟩
--      DFT arr (ι (cast refl p))
--    ≡⟨⟩
--      (DFT ∘ reshape eq) arr (ι (cast refl p))
--    ≡⟨ cong (λ f → (DFT ∘ reshape eq) arr (ι f)) (cast-is-id refl p ) ⟩
--      (DFT ∘ reshape eq) arr (ι p)
--    ∎
--  }
--theorm {s ⊗ s₁} arr = ?
--
--theorm₂ : ∀ {s : Shape} (arr : Ar s ℂ) (p : Position (ι (length s)))
--  → ((reshape _♭ ∘ FFT) arr) (lemma₂ {s} p) ≡ (DFT ∘ (reshape {s} (_♭))) arr p
--theorm₂ {ι n   } arr (ι p) rewrite cast-is-id refl p = refl
--theorm₂ {s ⊗ s₁} arr (ι p) =
--  begin
--    (reshape (flat ∙ _♭ ⊕ _♭) ∘ FFT) arr (ι (cast (lemma₁ {s ⊗ s₁}) p))
--  ≡⟨⟩
--    (reshape (flat ∙ _♭ ⊕ _♭) (FFT arr)) (ι (cast (lemma₁ {s ⊗ s₁}) p))
--  ≡⟨⟩
--    reshape (flat ∙ _♭ ⊕ _♭)
--            (reshape 
--              swap 
--              (nestedMap 
--                FFT 
--                (zipWith 
--                  _*_ 
--                  (reshape swap (nestedMap FFT (reshape swap arr)))
--                  twiddles
--                )
--              )
--            )
--            (ι (cast (lemma₁ {s ⊗ s₁}) p))
--  ≡⟨ cong ? ? ⟩
--    reshape (flat ∙ _♭ ⊕ _♭)
--            (reshape 
--              swap 
--              (nestedMap 
--                (?) 
--                (zipWith 
--                  _*_ 
--                  (reshape swap (nestedMap FFT (reshape swap arr)))
--                  twiddles
--                )
--              )
--            )
--            (ι (cast _ p))
--  ≡⟨⟩
--    ?
--
--
--theorm₃ : ∀ {s : Shape}
--  → (λ arr → ((reshape _♭ ∘ FFT) arr) ∘ lemma₂ {s}) ≡ (DFT ∘ (reshape {s} (_♭)))
--theorm₃ {ι x} =
--  extensionality λ{ arr →
--    extensionality λ{ (ι p) →
--      begin
--        (FFT arr ∘ (lemma₂ {ι x})) (ι p)
--      ≡⟨⟩
--        (FFT arr) (ι (cast refl p))
--      ≡⟨ cong (λ f → (FFT arr) (ι f)) (cast-is-id refl p) ⟩
--        (FFT arr) (ι p)
--      ≡⟨⟩
--        (DFT arr) (ι p)
--      ∎
--    }
--  }
--theorm₃ {s ⊗ s₁} =
--  extensionality λ{ arr →
--    extensionality λ{ (ι p) →
--      begin
--        ((reshape (flat ∙ _♭ ⊕ _♭) ∘ FFT) arr ∘ lemma₂ {s ⊗ s₁}) (ι p)
--      ≡⟨⟩
--        reshape (flat ∙ _♭ ⊕ _♭)
--            (reshape swap
--             (nestedMap FFT
--              (zipWith _*_ (reshape swap (nestedMap FFT (reshape swap arr)))
--               twiddles)))
--            (lemma₂ {s ⊗ s₁} (ι p))
--      ≡⟨⟩
--        ?
--    }
--  }



--  $ (FFT giant-fft-in-order)
--  --$ (DFT ∘ reshape (_♭)) giant-fft-in-order
--showProofRight : IO {a} ⊤
--showProofRight = putStrLn $ showMatrix showComplex 
--  $ reshape {ι 16 } {recursive-transpose (ι 4 ⊗ (ι 2 ⊗ ι 2))} _♯ ((DFT ∘ (reshape {ι 4 ⊗ (ι 2 ⊗ ι 2) } (_♭))) giant-fft-in-order) 


  --≡⟨ cong (λ f → (reshape (flat ∙ _♭ ⊕ _♭) ∘ FFT) arr (ι f)) (?) ⟩
  --  (reshape (flat ∙ _♭ ⊕ _♭) ∘ FFT) arr (ι (?))
  --≡⟨⟩
  --  ?

{-
theorm : ∀ {s : Shape} (arr : Ar s ℂ) → (pos : Fin (length s))
  → (DFT (reshape {s} (_♭) arr)) (ι pos) ≡ (reshape _♭ (FFT arr)) (ι (cast (lemma₁ {s}) pos))
theorm {ι .(suc _)} arr fzero = refl
theorm {ι .(suc _)} arr (fsuc pos) = ?
theorm {s ⊗ s₁} arr pos = ?
-}



--reshape-length : {s : Shape} → Reshape (ι $ length $ recursive-transpose s) (ι $ length s)
--reshape-length {ι x} = eq
--reshape-length {s ⊗ s₁} = flat ∙ swap ∙ reshape-length {s₁} ⊕ reshape-length {s} ∙ split
--
--lemma₂ : ∀ {s : Shape} → Fin (length (recursive-transpose s)) ≡ Fin (length s)
--lemma₂ {s} rewrite lemma₁ {s} = refl
--
--
---- TAKEN FROM CODE SHARED TO BE BY Artem, if I wish to include this I must thus cite it
--module equality
--  where
--    private variable
--      m n : ℕ
--      s p q u : Shape
--
--    ι-injₛ : _≡_ {A = Shape} (ι m) (ι n) → m ≡ n
--    ι-injₛ refl = refl
--
--    s-eq-proj₁ : _≡_ {A = Shape} (s ⊗ p) (q ⊗ u) → s ≡ q
--    s-eq-proj₁ refl = refl
--
--    s-eq-proj₂ : _≡_ {A = Shape} (s ⊗ p) (q ⊗ u) → p ≡ u
--    s-eq-proj₂ refl = refl
--
--    _≟ₛ_ : (s p : Shape) → Dec (s ≡ p)
--    ι m ≟ₛ ι n with m ≟ n
--    ... | yes refl = yes refl
--    ... | no ¬p = no λ p → ¬p (ι-injₛ p)
--    ι x ≟ₛ (p ⊗ p₁) = no (λ ())
--    (s ⊗ s₁) ≟ₛ ι x = no (λ ())
--    (s ⊗ q) ≟ₛ (p ⊗ w) with s ≟ₛ p | q ≟ₛ w
--    ... | yes a | yes b = yes (cong₂ _⊗_ a b)
--    ... | yes a | no ¬b = no λ p → ¬b (s-eq-proj₂ p)
--    ... | no ¬a | _     = no λ p → ¬a (s-eq-proj₁ p)
--
--open equality
--
--tmp₁ : ∀ {s : Shape} → Ar s ℂ → Ar (ι (length s)) ℂ 
--tmp₁ arr (ι x) = ((DFT ∘ reshape (_♭)) arr) (ι x)

--tmp₂ : ∀ {s : Shape} → Ar s ℂ → Ar (ι (length s)) ℂ 
----tmp₂ {s} arr (ι x) with lemma₂ {s}
----... | prf rewrite prf = (reshape (_♭) (FFT arr)) (ι x)
----tmp₂ {s} arr (ι x) rewrite lemma₂ {s} = (reshape (_♭) (FFT arr)) (ι x)
--tmp₂ {s} arr (ι x) rewrite lemma₂ {s} = (reshape (_♭) (FFT arr)) (ι x)

--tmp₃ : ∀ {s : Shape} → Ar (ι (length s)) ℂ → Ar (ι (length (recursive-transpose s))) ℂ 
--tmp₃ {s} arr (ι x) rewrite lemma₂ {s} = arr (ι x)
--tmp₃ {s} arr (ι x) rewrite lemma₂ {s} = arr (ι ?)
--((cast {length s} {length (recursive-transpose s)})


--theorm : ∀ {s : Shape} {arr : Ar s ℂ} {pos : Position (ι (length s))} →  (DFT ∘ reshape (_♭)) arr pos ≡ (reshape (_♭ ∙ recursive-transposeᵣ) ∘ FFT {s}) arr pos
--theorm {s} {arr} {ι x} = ?
--theorm {s} {arr} {pos} =
--  begin
--    ( reshape (_♯ ∙ reshape-length {s}) 
--    ∘ DFT 
--    ∘ reshape (_♭ ∙ recursive-transposeᵣ)
--    ) arr pos
--  ≡⟨⟩
--    ( reshape _♯
--    ∘ reshape (reshape-length {s}) 
--    ∘ DFT 
--    ∘ reshape _♭ 
--    ∘ reshape recursive-transposeᵣ
--    ) arr pos
--  ≡⟨ cong (λ f → ( reshape _♯ ∘ reshape f ∘ DFT ∘ reshape _♭ ∘ reshape recursive-transposeᵣ) arr pos) (?) ⟩
--    ( reshape _♯
--    ∘ reshape (?) 
--    ∘ DFT 
--    ∘ reshape _♭ 
--    ∘ reshape recursive-transposeᵣ
--    ) arr pos
--  ≡⟨⟩
--    ?
    
--atheorm : ∀ {s : Shape} → FFT {s} ≡ (reshape (_♯) ∘ DFT ∘ reshape {s} (_♭ ∙ recursive-transposeᵣ))
--btheorm : ∀ {s : Shape} →  (DFT ∘ reshape {s} (_♭ ∙ recursive-transposeᵣ )) ≡ ?
-- showProofLeft  : IO {a} ⊤
-- showProofLeft  = putStrLn $ showMatrix showComplex 
--   $ reshape (_♭ ) (FFT giant-fft-half-split)
-- showProofRight : IO {a} ⊤
-- showProofRight = putStrLn $ showMatrix showComplex $ DFT (reshape (_♭ ∙ recursive-transposeᵣ) giant-fft-half-split)

{- 
sub-θ : {s s₁ : Shape} (pos : Position (ι (length s))) → (p : Fin (length s *ₙ length s₁)) → ℝ 
sub-θ {s} {s₁} pos p = (((posVec pos *ₙ toℕ (proj₂ (quotRem {length s} (length s₁) p))) ᵣ) /ᵣ (length s ᵣ))

lemma₈ : 
  ∀ {n m : ℕ} {arr : Ar (ι (suc n) ⊗ ι m) ℂ} 
  → (flt : Reshape (ι (suc n) ⊗ ι m) (ι ((suc n) *ₙ m)) )
  → (fun : ℂ → ℂ)
  →   foldr _+_ (ℂfromℕ 0) (λ p → f ((reshape flt arr) p))
    ≡
      foldr _+_ (ℂfromℕ 0) (λ p → (foldr _+_ (ℂfromℕ 0)) ((nest arr) p))
lemma₈ {n} {m} {arr} flt = ?

theorm₈ : ∀ {n : ℕ} {m : ℕ} → (DFT ∘ reshape (_♭ {ι (suc n) ⊗ ι m})) ≡ FFT₁ {ι (suc n) ⊗ ι m}
theorm₈ {n} {m} =
  extensionality λ{ arr → 
    extensionality λ{ (ι p) → 
      let ⟨ y , x ⟩ = quotRem {suc n} m p in 
      begin
        (DFT ∘ reshape (flat ∙ eq ⊕ eq )) arr (ι p)
      ≡⟨ cong (λ f → (DFT ∘ reshape flat) f (ι p)) (eq+eq arr) ⟩
        (DFT ∘ reshape flat) arr (ι p)
      ≡⟨⟩
        (DFT (reshape flat arr)) (ι p)
      ≡⟨⟩
        foldr _+_ (ℂfromℕ 0) (zipWith step (reshape flat arr) posVec)
      ≡⟨⟩
        foldr _+_ (ℂfromℕ 0) (((λ flattened_arr → (λ pos → (step {(suc n) *ₙ m} {p} (flattened_arr pos) (posVec pos)))) ∘ (reshape flat)) arr)
      ≡⟨ lemma₈ {n} {m} {?} flat ? ⟩
        ?
    }
  }
--ι i         ⟨ flat   ⟩ = let a , b = remQuot _ i in ι a ⊗ ι b

FFT₁≡FFT : ∀ {s : Shape} → FFT₁ {s} ≡ reshape (_♭ ∙ (rev recursive-transposeᵣ)) ∘ FFT {s} 
FFT₁≡FFT {ι x} = refl
FFT₁≡FFT {s ⊗ s₁} =
  extensionality λ{ arr → 
    extensionality λ{ (ι p) → 
      ?
    }
  }

--tmp : ∀ {quotRem : ℕ} {real-arr complex-arr : Ar (ι n) ℝ} 
--                                                           +
--    foldr {n} _+ᵣ_         (0 ᵣ)   (λ pos →                  (complex-arr pos)) i
--tmp {zero } {real-arr} {complex-arr} = refl
--tmp {suc n} {real-arr} {complex-arr} =
--  begin
--    foldr _+_
--            (head₁ (λ pos → real-arr pos + complex-arr pos i) + ((0 ᵣ) + 0 ᵣ i))
--            (tail₁ (λ pos → real-arr pos + complex-arr pos i))
--  ≡⟨ tmp {?} {?} {?} ⟩
--    ?

-- TODO: Prove this (however that requires assoc and comm proofs for complex so will push till I know I need this
foldr-lemma₂ : ∀ {n : ℕ} {val acc : ℂ} {arr : Ar (ι n) ℂ} → foldr {n} _+_ (val + acc) arr ≡ val + (foldr {n} _+_ acc arr)
tail-ι-cons : ∀ {X : Set} {n : ℕ} {x : X} {xs : Ar (ι n) X} → tail₁ (ι-cons x xs) ≡ xs
prf : ∀ {n : ℕ} {real-arr complex-arr : Ar (ι (suc n)) ℝ}
    →
      (λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i)
    ≡ 
      (tail₁ (λ pos → real-arr pos + complex-arr pos i))
--prf {n} {real-arr} {complex-arr} =
--  begin
--    (λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i)
--   ≡⟨ sym (tail-ι-cons {ℂ} {n} {head₁ real-arr + head₁ complex-arr i} {λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i }) ⟩
--     tail₁ (ι-cons (head₁ real-arr + head₁ complex-arr i) (λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i))
--  ≡⟨⟩
--     tail₁ (ι-cons (head₁ real-arr + head₁ complex-arr i) (λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i))
--  ≡⟨⟩
--    ?
foldr-lemma₁ : ∀ {n : ℕ} {val acc : ℝ} {arr : Ar (ι n) ℝ} → foldr {n} _+ᵣ_ (val +ᵣ acc) arr ≡ val +ᵣ (foldr {n} _+ᵣ_ acc arr)
foldr-lemma₁ {zero } {val} {acc} {arr} = refl
foldr-lemma₁ {suc n} {val} {acc} {arr} =
  begin
    foldr _+ᵣ_ ((head₁ arr) +ᵣ (val +ᵣ acc)) (tail₁ arr)
  ≡⟨ cong (λ f → foldr _+ᵣ_ (f) (tail₁ arr)) (+ᵣ-comm (head₁ arr) (val +ᵣ acc)) ⟩
    foldr _+ᵣ_ ((val +ᵣ acc) +ᵣ head₁ arr) (tail₁ arr)
  ≡⟨ cong (λ f → foldr _+ᵣ_ (f) (tail₁ arr)) (+ᵣ-assoc val acc (head₁ arr)) ⟩
    foldr _+ᵣ_ (val +ᵣ (acc +ᵣ head₁ arr)) (tail₁ arr)
  ≡⟨ foldr-lemma₁ {n} {val} {acc +ᵣ head₁ arr} {tail₁ arr} ⟩
    (val +ᵣ foldr _+ᵣ_ (acc +ᵣ head₁ arr) (tail₁ arr))
  ≡⟨ cong (λ f → val +ᵣ (foldr _+ᵣ_ (f) (tail₁ arr))) (+ᵣ-comm acc (head₁ arr)) ⟩
    (val +ᵣ foldr _+ᵣ_ (head₁ arr +ᵣ acc) (tail₁ arr))
  ∎

+-in-ℂ-folding : ∀ {r₁ r₂ c₁ c₂ : ℝ} → (r₁ +ᵣ r₂) + (c₁ +ᵣ c₂) i ≡ (r₁ + c₁ i) + (r₂ + c₂ i)
+-in-ℂ-folding {r₁} {r₂} {c₁} {c₂} = refl

merge-foldr : ∀ {n : ℕ} {real-arr complex-arr : Ar (ι n) ℝ} 
  → foldr {n} _+ᵣ_  (0 ᵣ)          (λ pos → (real-arr pos)                       )
                                                           +
    foldr {n} _+ᵣ_         (0 ᵣ)   (λ pos →                  (complex-arr pos)) i
  ≡
    foldr {n} _+_  ((0 ᵣ) + 0 ᵣ i) (λ pos → (real-arr pos) + (complex-arr pos)  i) 
merge-foldr {zero} {real-arr} {complex-arr} = refl
merge-foldr {suc n} {real-arr} {complex-arr} =
  begin
      (foldr _+ᵣ_ (head₁ real-arr    +ᵣ (0 ᵣ)) (tail₁ real-arr   ) 
    + 
       foldr _+ᵣ_ (head₁ complex-arr +ᵣ (0 ᵣ)) (tail₁ complex-arr) 
    i)
  ≡⟨ cong (λ f → (f) + foldr _+ᵣ_ (head₁ complex-arr +ᵣ (0 ᵣ)) (tail₁ complex-arr) i) (foldr-lemma₁ {n} {head₁ real-arr} {0 ᵣ} {tail₁ real-arr}) ⟩
      (((head₁ real-arr) +ᵣ (foldr _+ᵣ_ ((0 ᵣ)) (tail₁ real-arr   )))
    + 
       foldr _+ᵣ_ (head₁ complex-arr +ᵣ (0 ᵣ)) (tail₁ complex-arr) 
    i)
  ≡⟨ cong (λ f → ((head₁ real-arr) +ᵣ (foldr _+ᵣ_ ((0 ᵣ)) (tail₁ real-arr   ))) + (f) i) (foldr-lemma₁ {n} {head₁ complex-arr} {0 ᵣ} {tail₁ complex-arr}) ⟩
      (((head₁ real-arr   ) +ᵣ (foldr _+ᵣ_ ((0 ᵣ)) (tail₁ real-arr   )))
    + 
       ((head₁ complex-arr) +ᵣ (foldr _+ᵣ_ ((0 ᵣ)) (tail₁ complex-arr)))
    i)
  ≡⟨⟩
    ((head₁ real-arr) + (head₁ complex-arr) i)
      +
    (   (foldr _+ᵣ_ (0 ᵣ) (tail₁ real-arr   ))
      +
        (foldr _+ᵣ_ (0 ᵣ) (tail₁ complex-arr))
      i
    )
  ≡⟨ cong (λ f → ((head₁ real-arr) + (head₁ complex-arr) i) + (f)) (merge-foldr {n} {tail₁ real-arr} {tail₁ complex-arr}) ⟩
    (head₁ real-arr + head₁ complex-arr i)
      +
    foldr _+_ ((0 ᵣ) + 0 ᵣ i) (λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i)
  ≡⟨ sym (foldr-lemma₂ {n} {(head₁ real-arr) + (head₁ complex-arr) i} {(0 ᵣ) + 0 ᵣ i} {λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i }) ⟩
    foldr _+_ 
      ((head₁ real-arr + head₁ complex-arr i) + ((0 ᵣ) + 0 ᵣ i))
      (λ pos → tail₁ real-arr pos + tail₁ complex-arr pos i)
  ≡⟨ cong (λ f → foldr _+_ ((head₁ real-arr + head₁ complex-arr i) + ((0 ᵣ) + 0 ᵣ i)) (f)) (prf {n} {real-arr} {complex-arr}) ⟩
    foldr _+_ 
      ((head₁ real-arr + head₁ complex-arr i) + ((0 ᵣ) + 0 ᵣ i))
      (tail₁ (λ pos → real-arr pos + complex-arr pos i))
  ∎
  
    

      
--foldr-lemma₁ : ∀ {n : ℕ} {val acc : ℝ} {arr : Ar (ι n) ℝ} → foldr {n} _+ᵣ_ (val +ᵣ acc) arr ≡ val +ᵣ (foldr {n} _+ᵣ_ acc arr)
    
      

theorm₇ : ∀ {s : Shape} → FFT₁ {s} ≡ (DFT ∘ reshape _♭)
theorm₇ {ι x} = refl
theorm₇ {s₀ ⊗ s₁} =
  extensionality λ{ arr → 
    extensionality λ{ (ι p) → 
      begin
        FFT₁ arr (ι p)
      ≡⟨⟩
        reshape 
          (flat ∙ swap)
          (nestedMap FFT₁ 
            (reshape 
              swap 
              (zipWith _*_ (nestedMap FFT₁ arr) twiddles)
            )
          )
          (ι p)
      ≡⟨ cong (λ f → reshape (flat ∙ swap) (nestedMap FFT₁ (reshape swap (zipWith _*_ (nestedMap f arr) twiddles))) (ι p)) theorm₇ ⟩
        reshape 
          (flat ∙ swap)
          (nestedMap FFT₁ 
            (reshape 
              swap 
              (zipWith _*_ (nestedMap (DFT ∘ reshape _♭) arr) twiddles)
            )
          )
          (ι p)
      ≡⟨ cong (λ f → reshape (flat ∙ swap) (nestedMap f (reshape swap (zipWith _*_ (nestedMap (DFT ∘ reshape _♭) arr) twiddles))) (ι p)) theorm₇ ⟩
        reshape 
          (flat ∙ swap)
          (nestedMap (DFT ∘ reshape _♭)
            (reshape 
              swap 
              (zipWith _*_ (nestedMap (DFT ∘ reshape _♭) arr) twiddles)
            )
          )
          (ι p)
      ≡⟨⟩
        map DFT (
        map (reshape _♭) (
          nest (reshape swap (zipWith _*_ (unnest (map DFT (map (reshape _♭) (nest arr)))) twiddles))
        )) (ι j₁) (ι j₀)
      ≡⟨⟩
        foldr _+_ ((0 ᵣ) + 0 ᵣ i)
            (λ pos →
               ((((real      (innerDFT arr pos p) *ᵣ cos (θ₂ pos p))
                  -ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p)))
                 *ᵣ cos (θ pos p))
                -ᵣ
                (((real      (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))
                  +ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)))
                 *ᵣ sin (θ pos p)))
               +
                (((real      (innerDFT arr pos p) *ᵣ cos (θ₂ pos p))
                  -ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p)))
                 *ᵣ sin (θ pos p))
                +ᵣ
                (((real      (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))
                  +ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)))
                 *ᵣ cos (θ pos p))
               i)
      ≡⟨ sym (merge-foldr {length s₀} {
          (λ pos → ((((real      (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)) -ᵣ (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))) *ᵣ cos (θ pos p)) -ᵣ (((real      (innerDFT arr pos p) *ᵣ sin (θ₂ pos p)) +ᵣ (imaginary (innerDFT arr pos p) *ᵣ cos (θ₂ pos p))) *ᵣ sin (θ pos p))))
        } {
          (λ pos → (((real      (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)) -ᵣ (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))) *ᵣ sin (θ pos p)) +ᵣ (((real      (innerDFT arr pos p) *ᵣ sin (θ₂ pos p)) +ᵣ (imaginary (innerDFT arr pos p) *ᵣ cos (θ₂ pos p))) *ᵣ cos (θ pos p)))
        }) ⟩
        foldr _+ᵣ_ (0 ᵣ)
            (λ pos →
               ((((real      (innerDFT arr pos p) *ᵣ cos (θ₂ pos p))
                  -ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p)))
                 *ᵣ cos (θ pos p))
                -ᵣ
                (((real      (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))
                  +ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)))
                 *ᵣ sin (θ pos p)))
               )
       +
        foldr _+ᵣ_ (0 ᵣ)
            (λ pos →
                (((real      (innerDFT arr pos p) *ᵣ cos (θ₂ pos p))
                  -ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p)))
                 *ᵣ sin (θ pos p))
                +ᵣ
                (((real      (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))
                  +ᵣ
                  (imaginary (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)))
                 *ᵣ cos (θ pos p))
               )
       i
          ≡⟨⟩
            ? -- TODO: Talk to Artjoms about where to go from here, stuck at this stage and this split hasn't really helped me
    }
  }
  where
    j₀ : {p : Position (ι (length s₀ *ₙ length s₁))} → Fin (length s₀)
    j₀ {ι p} = proj₂ (quotRem {length s₀} (length s₁) p)
    j₁ : {p : Position (ι (length s₀ *ₙ length s₁))} → Fin (length s₁)
    j₁ {ι p} = proj₁ (quotRem {length s₀} (length s₁) p)

    θ : (pos : Position (ι (length s₀))) → (p : Fin (length s₀ *ₙ length s₁)) → ℝ
    θ pos p = ((-ᵣ 2 ᵣ *ᵣ π *ᵣ (posVec pos *ₙ toℕ j₀) ᵣ) /ᵣ (length s₀ ᵣ))

    θ₂ : (pos : Position (ι (length s₀))) → (p : Fin (length s₀ *ₙ length s₁)) → ℝ
    θ₂ pos p = (-ᵣ 2 ᵣ *ᵣ π *ᵣ
                    (position-sum {s₀} (pos ⟨ _♭ ⟩) *ₙ
                     position-sum (ι (j₁)))
                    ᵣ)
                   /ᵣ ((length s₀ *ₙ length s₁) ᵣ)
    innerDFT : (arr : Ar (s₀ ⊗ s₁) ℂ) → (pos : Position (ι (length s₀))) → (p : Fin (length s₀ *ₙ length s₁)) → ℂ
    innerDFT arr pos p = (foldr _+_ ((0 ᵣ) + 0 ᵣ i)
                    (λ pos₁ →
                       ((real (arr ((pos ⟨ _♭ ⟩) ⊗ (pos₁ ⟨ _♭ ⟩))) *ᵣ
                         cos
                         ((-ᵣ 2 ᵣ *ᵣ π *ᵣ
                           (posVec pos₁ *ₙ toℕ (j₁)) ᵣ)
                          /ᵣ (length s₁ ᵣ)))
                        -ᵣ
                        (imaginary (arr ((pos ⟨ _♭ ⟩) ⊗ (pos₁ ⟨ _♭ ⟩))) *ᵣ
                         sin
                         ((-ᵣ 2 ᵣ *ᵣ π *ᵣ
                           (posVec pos₁ *ₙ toℕ (j₁)) ᵣ)
                          /ᵣ (length s₁ ᵣ))))
                       +
                       (real (arr ((pos ⟨ _♭ ⟩) ⊗ (pos₁ ⟨ _♭ ⟩))) *ᵣ
                        sin
                        ((-ᵣ 2 ᵣ *ᵣ π *ᵣ
                          (posVec pos₁ *ₙ toℕ (j₁)) ᵣ)
                         /ᵣ (length s₁ ᵣ)))
                       +ᵣ
                       (imaginary (arr ((pos ⟨ _♭ ⟩) ⊗ (pos₁ ⟨ _♭ ⟩))) *ᵣ
                        cos
                        ((-ᵣ 2 ᵣ *ᵣ π *ᵣ
                          (posVec pos₁ *ₙ toℕ (j₁)) ᵣ)
                         /ᵣ (length s₁ ᵣ)))
                       i))
    --hypothetical : (arr : Ar (s₀ ⊗ s₁) ℂ) → (pos : Position (ι (length s₀))) → (p : Fin (length s₀ *ₙ length s₁)) → 
    --    (((real (innerDFT arr pos p) *ᵣ cos (θ₂ pos p)) -ᵣ (imaginary (innerDFT arr pos p) *ᵣ sin (θ₂ pos p))) *ᵣ cos (θ pos p))
    --  ≡
    --    (real (arr ((pos ⟨ flat ⟩) ⟨ _♭ ⊕ _♭ ⟩)) *ᵣ cos ((-ᵣ 2 ᵣ *ᵣ π *ᵣ (posVec pos *ₙ toℕ p) ᵣ) /ᵣ ((length s₀ *ₙ length s₁) ᵣ)))




-- lemma₁ : ∀ 
--   {s s₁ : Shape}
--   {pos  : Position (ι (length s₁))}
--   {p    : Fin (length s *ₙ length s₁)}
--   → 
--     (((posVec pos *ₙ toℕ                                        p)   ᵣ) /ᵣ ((length s *ₙ length s₁) ᵣ)) 
--   ≡ 
--     (((posVec pos *ₙ toℕ {length s} (proj₂ (quotRem {length s} (length s₁) p))) ᵣ) /ᵣ ( length s               ᵣ))
-- lemma₁ {s} {s₁} {ι x} {p} =
--   begin
--     (((posVec (ι x) *ₙ toℕ p) ᵣ) /ᵣ ((length s *ₙ length s₁) ᵣ))
--   ≡⟨⟩
--     (((toℕ x *ₙ toℕ p) ᵣ) /ᵣ ((length s *ₙ length s₁) ᵣ))
--   ≡⟨⟩
--     ?

-}




