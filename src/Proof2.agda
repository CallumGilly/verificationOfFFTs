open import src.Real.Base using (RealBase)
open import src.Complex.Base using (CplxBase)

open import src.Real.Properties using (RealProperties)
open import src.Complex.Properties using (CplxProperties)

module src.Proof2 
  (realBase : RealBase)
  (realProperties : RealProperties realBase)
  (cplxBase : CplxBase realBase)
  (cplxProperties : CplxProperties realBase cplxBase)
  where

open CplxBase cplxBase using (ℂ; _*_; _+_; ℂfromℕ; -ω)
open CplxProperties cplxProperties using (+-identityʳ; ω-N-0; *-identityʳ; *-assoc; *-zeroˡ)
--(;)
open RealBase realBase using (ℝ; π; sin; cos; _ᵣ)
  renaming (_+_ to _+ᵣ_; _-_ to _-ᵣ_; -_ to -ᵣ_; _/_ to _/ᵣ_; _*_ to _*ᵣ_)
--open RealProperties realProperties using (double-negative; *ᵣ-zeroᵣ; +ᵣ-identityˡ; *ᵣ-identityʳ; /ᵣ-zeroₜ; +ᵣ-identityʳ; +ᵣ-assoc; +ᵣ-comm)

open import Data.Nat.Base using (ℕ; suc; zero) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties using (*-comm; _≟_) renaming (*-zeroʳ to *ₙ-zeroʳ; *-zeroˡ to *ₙ-zeroˡ)
open import Data.Fin.Base using (Fin; quotRem; toℕ; combine; remQuot; quotient; remainder; cast) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (cast-is-id)
open import Data.Product.Base using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩)

open import src.Matrix using (Ar; Shape; _⊗_; ι; Position; nestedMap; zipWith; nest; map; unnest; head₁; tail₁; zip; iterate; ι-cons; nil; foldr; length; cong-foldr)
open import src.Reshape using (reshape; Reshape; flat; _♭; _♯; recursive-transpose; recursive-transposeᵣ; _∙_; rev; _⊕_; swap; eq; split; _⟨_⟩; eq+eq; _♭₂; comm-eq; eq+eq-position-wrapper)
--open ℂ using (real; imaginary)
open import src.FFT realBase cplxBase using (FFT; twiddles; position-sum; offset-n)
open import src.DFTMatrix realBase cplxBase using (DFT; posVec; step)
open import src.Extensionality using (extensionality)
open import Relation.Nullary using (Dec; yes; no)

open import Function.Base using (_$_; id; _∘_; flip; _∘₂_)

open import src.MatrixEquality as MatEq
open MatEq using (_≅_; mat-refl)
open MatEq.≅-Reasoning


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; subst; cong-app)
open Eq.≡-Reasoning

private variable
  r₁ r₂ : ℕ
  arr : Ar (ι r₁ ⊗ ι r₂) ℂ
  j₀ : Fin r₁
  j₁ : Fin r₂
  k₀ : Position (ι r₂)
  k₁ : Position (ι r₁)

dft-fold-equiv : ∀ 
  {n m : ℕ} 
  {arr : Ar (ι n ⊗ ι m) ℂ} 
  {x : Fin n} 
  {y : Fin m} 
  → 
  (((reshape _♯) ∘ DFT ∘ (reshape {ι n ⊗ ι m} _♭₂)) arr) (ι y ⊗ ι x) 
  ≡ 
    foldr 
      {m *ₙ n } 
      _+_ 
      (ℂfromℕ 0) 
      (λ absPos → 
        (arr (absPos ⟨ comm-eq (*-comm n m) ⟩ ⟨ flat ⟩)) 
        * 
        (-ω (m *ₙ n) ((posVec absPos) *ₙ (toℕ (combine y x))))
      )
dft-fold-equiv {n} {m} {arr} {x} {y} =
  begin
    (reshape _♯ ∘ DFT ∘ reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq)) arr (ι y ⊗ ι x)
  ≡⟨⟩
    (reshape _♯ (DFT (reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq) arr))) (ι y ⊗ ι x)
  ≡⟨⟩
    ((DFT (reshape (comm-eq (*-comm n m) ∙ flat ∙ eq ⊕ eq) arr))) ((ι y ⊗ ι x) ⟨ _♯ {ι m ⊗ ι n } ⟩ )
  ≡⟨⟩
    ((DFT (reshape (comm-eq (*-comm n m) ∙ flat) (reshape (eq ⊕ eq) arr)))) ((ι y ⊗ ι x) ⟨ _♯ {ι m ⊗ ι n } ⟩ )
  ≡⟨ cong
      (λ f → ((DFT (reshape (comm-eq (*-comm n m) ∙ flat) (f)))) ((ι y ⊗ ι x) ⟨ _♯ {ι m ⊗ ι n } ⟩ ))
      (eq+eq arr)
   ⟩
    ((DFT (reshape (comm-eq (*-comm n m) ∙ flat) arr))) ((ι y ⊗ ι x) ⟨ _♯ {ι m ⊗ ι n } ⟩ )
  ≡⟨⟩
    foldr {m *ₙ n } _+_ (ℂfromℕ 0) (zipWith step (reshape (comm-eq (*-comm n m) ∙ flat) arr) posVec)
  ≡⟨⟩
    foldr {m *ₙ n } _+_ (ℂfromℕ 0) (λ absPos → step (arr (absPos ⟨ comm-eq (*-comm n m) ⟩ ⟨ flat ⟩)) (posVec absPos))
  ≡⟨⟩
    foldr 
      {m *ₙ n } 
      _+_ 
      (ℂfromℕ 0) 
      (λ absPos → 
        (arr (absPos ⟨ comm-eq (*-comm n m) ⟩ ⟨ flat ⟩)) 
        * 
        (-ω (m *ₙ n) ((posVec absPos) *ₙ (toℕ (combine y x))))
      )
  ∎


postulate
  const*foldr : ∀ {n : ℕ} (ar : Ar (ι n) ℂ) (constant : ℂ) → (foldr _+_ (ℂfromℕ 0) (λ n → ar n)) * constant  ≡ foldr _+_ (ℂfromℕ 0) (λ n → constant * ar n)

theorm-inside-Σk₀ : ∀
  {r₁ r₂ : ℕ} 
  {arr : Ar (ι r₁ ⊗ ι r₂) ℂ} 
  {j₀ : Fin r₁} 
  {j₁ : Fin r₂} 
  (k₀ : Position (ι r₂))  
  →
        (
           foldr 
             _+_ 
             (ℂfromℕ 0) 
             (λ k₁ →  
               (arr (k₁ ⊗ k₀))
               * 
               (-ω (r₁) ((posVec k₁) *ₙ (posVec (ι j₀))))
             )
           *
             (-ω (r₁ *ₙ r₂) (position-sum ((ι j₀) ⊗ k₀)))
        )
      * 
        (-ω r₂ ((posVec k₀) *ₙ (posVec (ι j₁))))
    ≡
      foldr 
        _+_ 
        (ℂfromℕ 0) 
        (λ k₁ →  
            (-ω r₂ ((posVec k₀) *ₙ (posVec (ι j₁))))
          * 
          (
              (-ω (r₁ *ₙ r₂) (position-sum ((ι j₀) ⊗ k₀)))
            *
              (
                (arr (k₁ ⊗ k₀))
                * 
                (-ω (r₁) ((posVec k₁) *ₙ (posVec (ι j₀))))
              )
          )
        )
theorm-inside-Σk₀ {r₁} {r₂} {arr} {j₀} {j₁} k₀ =
  begin
      (
         foldr 
           _+_ 
           (ℂfromℕ 0) 
           (λ k₁ →  
             (arr (k₁ ⊗ k₀))
             * 
             (-ω (r₁) ((posVec k₁) *ₙ (posVec (ι j₀))))
           )
         *
           (-ω (r₁ *ₙ r₂) (position-sum ((ι j₀) ⊗ k₀)))
      )
    * 
      (-ω r₂ ((posVec k₀) *ₙ (posVec (ι j₁))))
  ≡⟨ cong (_* (-ω r₂ ((posVec k₀) *ₙ (posVec (ι j₁))))) (const*foldr (λ k₁ → (arr (k₁ ⊗ k₀)) * (-ω (r₁) ((posVec k₁) *ₙ (posVec (ι j₀))))) (-ω (r₁ *ₙ r₂) (position-sum ((ι j₀) ⊗ k₀)))) ⟩
    foldr 
      _+_ 
      (ℂfromℕ 0) 
      (λ k₁ →  
          (-ω (r₁ *ₙ r₂) (position-sum ((ι j₀) ⊗ k₀)))
        *
          (
            (arr (k₁ ⊗ k₀))
            * 
            (-ω (r₁) ((posVec k₁) *ₙ (posVec (ι j₀))))
          )
      )
    * 
      (-ω r₂ ((posVec k₀) *ₙ (posVec (ι j₁))))
  ≡⟨ const*foldr
      (λ k₁ →  (-ω (r₁ *ₙ r₂) (position-sum ((ι j₀) ⊗ k₀))) * ((arr (k₁ ⊗ k₀)) * (-ω (r₁) ((posVec k₁) *ₙ (posVec (ι j₀))))))
      (-ω r₂ ((posVec k₀) *ₙ (posVec (ι j₁))))
   ⟩
    foldr 
      _+_ 
      (ℂfromℕ 0) 
      (λ k₁ →  
          (-ω r₂ ((posVec k₀) *ₙ (posVec (ι j₁))))
        * 
        (
            (-ω (r₁ *ₙ r₂) (position-sum ((ι j₀) ⊗ k₀)))
          *
            (
              (arr (k₁ ⊗ k₀))
              * 
              (-ω (r₁) ((posVec k₁) *ₙ (posVec (ι j₀))))
            )
        )
      )
  ∎

theorm-on-folds : ∀ 
  {r₁ r₂ : ℕ} 
  {arr : Ar (ι r₁ ⊗ ι r₂) ℂ} 
  {j₀ : Fin r₁} 
  {j₁ : Fin r₂} 
  →
    foldr 
      _+_
      (ℂfromℕ 0)
      (λ k₀ →  
        (
           (
             foldr 
               _+_ 
               (ℂfromℕ 0) 
               (λ k₁ →  
                 (arr (k₁ ⊗ k₀))
                 * 
                 (-ω (r₁) ((posVec k₁) *ₙ (posVec (ι j₀))))
               )
           )
           *
           (-ω (r₁ *ₙ r₂) (position-sum ((ι j₀) ⊗ k₀)))
        )
        * (-ω r₂ ((posVec k₀) *ₙ (posVec (ι j₁))))
      )
  ≡
  foldr 
    _+_ 
    (ℂfromℕ 0) 
    (λ k → 
      (arr (k ⟨ comm-eq (*-comm r₁ r₂) ⟩ ⟨ flat ⟩)) 
      * 
      (-ω (r₂ *ₙ r₁) ((posVec k) *ₙ (toℕ (combine j₁ j₀))))
    )
theorm-on-folds {r₁} {r₂} {arr} {j₀} {j₁} =
  begin
    foldr 
      _+_
      (ℂfromℕ 0)
      (λ k₀ →  
        (
           foldr 
             _+_ 
             (ℂfromℕ 0) 
             (λ k₁ →  
               (arr (k₁ ⊗ k₀))
               * 
               (-ω (r₁) ((posVec k₁) *ₙ (posVec (ι j₀))))
             )
           *
             (-ω (r₁ *ₙ r₂) (position-sum ((ι j₀) ⊗ k₀)))
        )
        * (-ω r₂ ((posVec k₀) *ₙ (posVec (ι j₁))))
      )
   ≡⟨ cong (λ f → foldr _+_ (ℂfromℕ 0) (λ k₀ → f k₀)) (? theorm-inside-Σk₀)  ⟩
    foldr 
      _+_
      (ℂfromℕ 0)
      (λ k₀ →  
        foldr 
          _+_ 
          (ℂfromℕ 0) 
          (λ k₁ →  
              (-ω r₂ ((posVec k₀) *ₙ (posVec (ι j₁))))
            * 
            (
                (-ω (r₁ *ₙ r₂) (position-sum ((ι j₀) ⊗ k₀)))
              *
                (
                  (arr (k₁ ⊗ k₀))
                  * 
                  (-ω (r₁) ((posVec k₁) *ₙ (posVec (ι j₀))))
                )
            )
          )
      )
   ≡⟨⟩
    ?

theorm : ∀ {r₁ r₂ : ℕ}
  → FFT ≡ (reshape _♯) ∘ DFT ∘ (reshape {ι r₁ ⊗ ι r₂} _♭₂)
theorm {r₁} {r₂} =
  extensionality λ{arr → 
    extensionality λ{ (ι j₁ ⊗ ι j₀) →
      begin
        (FFT arr) ((ι j₁) ⊗ (ι j₀))
      --≡⟨ fft₂-fold-equiv {r₁} {r₂} {arr} {j₀} {j₁} ⟩
      ≡⟨⟩
        foldr 
          _+_
          (ℂfromℕ 0)
          (λ k₀ →  
            (
               (
                 foldr 
                   _+_ 
                   (ℂfromℕ 0) 
                   (λ k₁ →  
                     (arr (k₁ ⊗ k₀))
                     * 
                     (-ω (r₁) ((posVec k₁) *ₙ (posVec (ι j₀))))
                   )
               )
               *
               (-ω (r₁ *ₙ r₂) (position-sum ((ι j₀) ⊗ k₀)))
            )
            * (-ω r₂ ((posVec k₀) *ₙ (posVec (ι j₁))))
          )
      ≡⟨ theorm-on-folds {r₁} {r₂} {arr} {j₀} {j₁} ⟩
        foldr 
          {r₂ *ₙ r₁ } 
          _+_ 
          (ℂfromℕ 0) 
          (λ absPos → 
            (arr (absPos ⟨ comm-eq (*-comm r₁ r₂) ⟩ ⟨ flat ⟩)) 
            * 
            (-ω (r₂ *ₙ r₁) ((posVec absPos) *ₙ (toℕ (combine j₁ j₀))))
          )
      ≡⟨ sym (dft-fold-equiv {r₁} {r₂} {arr} {j₀} {j₁}) ⟩
        (reshape _♯ ∘ DFT ∘ reshape (comm-eq (*-comm r₁ r₂) ∙ flat ∙ eq ⊕ eq)) arr (ι j₁ ⊗ ι j₀)
      ∎

    }
  }
 
 
{-
-- Lifted from Proof.agda
fft₂-fold-equiv : ∀ {r₁ r₂ : ℕ} {arr : Ar (ι r₁ ⊗ ι r₂) ℂ} {j₀ : Fin r₁} {j₁ : Fin r₂} →
  (FFT arr) ((ι j₁) ⊗ (ι j₀)) ≡
    foldr 
      _+_
      (ℂfromℕ 0)
      (λ k₀ →  
        (
           (
             foldr 
               _+_ 
               (ℂfromℕ 0) 
               (λ k₁ →  
                 (arr (k₁ ⊗ k₀))
                 * 
                 (-ω (r₁) ((posVec k₁) *ₙ (posVec (ι j₀))))
               )
           )
           *
           (-ω (r₁ *ₙ r₂) (position-sum ((ι j₀) ⊗ k₀)))
        )
        * (-ω r₂ ((posVec k₀) *ₙ (posVec (ι j₁))))
      )
fft₂-fold-equiv {r₁} {r₂} {arr} {j₀} {j₁} =
  begin
    (FFT arr) ((ι j₁) ⊗ (ι j₀))
  ≡⟨⟩
    reshape swap
            (nestedMap (λ arr₁ → DFT arr₁)
             (zipWith _*_
              (reshape swap (nestedMap (λ arr₁ → DFT arr₁) (reshape swap arr)))
              twiddles))
            (ι j₁ ⊗ ι j₀)
  ≡⟨⟩
    ( 
      DFT 
      ((nest (zipWith 
        _*_ 
        (reshape swap (unnest (map DFT ( nest (reshape swap arr)))))
        twiddles
      )) (ι j₀))
    )
    (ι j₁)
  ≡⟨⟩
    foldr 
      _+_
      (ℂfromℕ 0)
      (zipWith 
        step
        (nest
         (zipWith 
            _*_
            (reshape swap (unnest (map DFT (nest (reshape swap arr)))))
            twiddles
         )
         (ι j₀))
        posVec)
  ≡⟨⟩
    foldr 
      _+_
      (ℂfromℕ 0)
      (zipWith 
        step
         (zipWith 
            _*_
            (nest (reshape swap (unnest (map DFT (nest (reshape swap arr))))) (ι j₀))
            (nest twiddles (ι j₀))
         )
        posVec)
  ≡⟨⟩
    foldr 
      _+_
      (ℂfromℕ 0)
      (zipWith 
        step
         (zipWith 
            _*_
            (λ p → DFT (nest (reshape swap arr) p) (ι j₀))
            (nest twiddles (ι j₀))
         )
        posVec)
  ≡⟨⟩
    foldr 
      _+_
      (ℂfromℕ 0)
      (λ p →  
        step
        ((zipWith 
           _*_
           (λ k₀ → 
             foldr 
               _+_ 
               (ℂfromℕ 0) 
               (zipWith 
                 step 
                 (nest (reshape swap arr) k₀) 
                 posVec
               )
           )
           (nest twiddles (ι j₀))
        ) p)
        (posVec p))
  ≡⟨⟩
    foldr 
      _+_
      (ℂfromℕ 0)
      (λ k₀ →  
        step
        ((
           _*_
           (
             foldr 
               _+_ 
               (ℂfromℕ 0) 
               (λ k₁ →  
                 step 
                 ((nest (reshape swap arr) k₀) k₁)
                 (posVec k₁)
               )
           )
           ((nest twiddles (ι j₀)) k₀)
        ) )
        (posVec k₀))
  ≡⟨⟩
    foldr 
      _+_
      (ℂfromℕ 0)
      (λ k₀ →  
        step
        (
           _*_
           (
             foldr 
               _+_ 
               (ℂfromℕ 0) 
               (λ k₁ →  
                 step 
                 ((arr) (k₁ ⊗ k₀))
                 (posVec k₁)
               )
           )
           ((nest twiddles (ι j₀)) k₀)
        )
        (posVec k₀)
      )
  ≡⟨⟩
    foldr 
      _+_
      (ℂfromℕ 0)
      (λ k₀ →  
        (
           (
             foldr 
               _+_ 
               (ℂfromℕ 0) 
               (λ k₁ →  
                 (arr (k₁ ⊗ k₀))
                 * 
                 (-ω (r₁) ((posVec k₁) *ₙ (posVec (ι j₀))))
               )
           )
           *
           (-ω (r₁ *ₙ r₂) (position-sum ((ι j₀) ⊗ k₀)))
        )
        * (-ω r₂ ((posVec k₀) *ₙ (posVec (ι j₁))))
      )
    ∎
-}




