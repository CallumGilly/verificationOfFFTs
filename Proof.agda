open import Real using (Real)
open import Complex using (Cplx)

import Algebra.Structures as AlgebraStructures
import Algebra.Definitions as AlgebraDefinitions

open import Relation.Nullary
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

module Proof (cplx : Cplx) where

open Cplx cplx

open AlgebraStructures  {A = ℂ} _≡_
open AlgebraDefinitions {A = ℂ} _≡_

open IsCommutativeRing +-*-isCommutativeRing hiding (trans; refl; sym)

open import Data.Nat.Base renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties renaming (*-comm to *ₙ-comm; *-identityʳ to *ₙ-identityʳ; *-assoc to *ₙ-assoc; 
  +-identityʳ to +ₙ-identityʳ; *-zeroˡ to *ₙ-zeroˡ; *-zeroʳ to *ₙ-zeroʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver 
open import Data.Fin.Base renaming (zero to fzero; suc to fsuc) hiding (_+_)
open import Data.Fin.Properties
open import Data.Empty

open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Data.Unit

open import Matrix 
open import Matrix.Equality 
open import Matrix.NonZero

import Matrix.Sum as S
open S _+_ 0ℂ +-isCommutativeMonoid using (merge-sum; sum-reindex; sum-swap)
sum = S.sum _+_ 0ℂ +-isCommutativeMonoid
sum-cong = S.sum-cong _+_ 0ℂ +-isCommutativeMonoid

open import Matrix.Reshape 
open import Function.Base

open import FFT cplx

private
  variable
    s p r₁ r₂ : Shape
    N M : ℕ

-----------------------------------------
--- Shorthands to improve readability ---
-----------------------------------------

infixl 5 _⊡_
_⊡_ = trans

infix 10 #_
#_ : Shape → ℕ
#_ = length 

infix 11 _ᵗ
_ᵗ : Shape → Shape
_ᵗ = recursive-transpose

nz-# : NonZeroₛ s → NonZero (length s)
nz-# = nonZeroₛ-s⇒nonZero-s

nzᵗ : NonZeroₛ s → NonZeroₛ (s ᵗ)
nzᵗ = nonZeroₛ-s⇒nonZeroₛ-sᵗ

rev-eq-applied : (rshp : Reshape r₂ r₁) (arr : Ar r₁ ℂ) → reshape (rshp ∙ rev rshp) arr ≅ arr 
rev-eq-applied rshp arr i = cong arr (rev-eq rshp i)

-------------------------------------------
--- 4 way associativity helper function ---
-------------------------------------------

assoc₄ : (a b c d : ℂ) → a * b * c * d ≡ a * (b * c * d)
assoc₄ a b c d rewrite
    *-assoc a b c
  | *-assoc a (b * c) d
  = refl

--------------------------
--- Properties of iota ---
--------------------------

iota-reindex : ∀ {i : Position (ι N)} → (prf : M ≡ N) → iota (i ⟨ reindex prf ⟩) ≡ iota i
iota-reindex refl = refl

iota-split : ∀ 
   (k₀   : Position (ι (# r₂)))
   (k₁   : Position (ι (# r₁)))
   → iota ((k₁ ⊗ k₀) ⟨ split ⟩) ≡ (# r₂ *ₙ iota k₁) +ₙ iota k₀
iota-split (ι k₀) (ι k₁) rewrite toℕ-combine k₁ k₀ = refl

-----------------------------
--- Congurance properties ---
-----------------------------

-ω-cong₂ : 
  ∀ {n m : ℕ} 
  → ⦃ nonZero-n : NonZero n ⦄
  → ⦃ nonZero-m : NonZero m ⦄
  → ∀ {k j : ℕ} 
  → (prfₗ : n ≡ m)
  → k ≡ j 
  → -ω n ⦃ nonZero-n ⦄ k ≡ -ω m ⦃ nonZero-m ⦄ j
-ω-cong₂ refl refl = refl

DFT-cong : ∀ {xs ys : Ar (ι N) ℂ} → xs ≅ ys → DFT xs ≅ DFT ys
DFT-cong {suc N}  prf (ι j) = sum-cong {suc N} (λ i → cong₂ _*_ (prf i) refl)

FFT-cong : ∀ {s : Shape} {xs ys : Ar s ℂ} → xs ≅ ys → FFT xs ≅ FFT ys
FFT-cong {ι N} = DFT-cong 
FFT-cong {r₁ ⊗ r₂} {xs} {ys} prf (j₁ ⊗ j₀) =
    (FFT-cong {r₂} λ{ k₀ → 
        (cong₂ _*_ 
          ((FFT-cong {r₁} λ{k₁ → 
            prf (k₁ ⊗ k₀) 
          }) j₀ ) 
          refl
        ) 
      }) j₁

-------------------------
--- Properties of Sum ---
-------------------------

-- Of note here is that I cannot put this in the sum module as it requires knowledge of _+_ as well as its relation with _*_

*-distribˡ-sum : {xs : Ar (ι N) ℂ} (x : ℂ) → x * (sum xs) ≡ sum (map (x *_) xs)
*-distribˡ-sum {zero} {xs} x = zeroʳ x
*-distribˡ-sum {suc N} {xs} x rewrite 
    distribˡ x (xs (ι fzero)) (sum (tail₁ xs)) 
  | *-distribˡ-sum {N} {tail₁ xs} x 
  = cong₂ _+_ refl (sum-cong {N} (λ{(ι i) → refl }))

*-distribʳ-sum : {xs : Ar (ι N) ℂ} (x : ℂ) → (sum xs) * x ≡ sum (map (_* x) xs)
*-distribʳ-sum {N} {xs} x rewrite
    *-comm (sum xs) x
  | *-distribˡ-sum {N} {xs} x
  = sum-cong {N} λ i → *-comm x (xs i)

------------------------------------
--- Rearanging of roots of unity ---
------------------------------------
cooley-tukey-derivation : 
  ∀ (r₁ r₂ k₀ k₁ j₀ j₁ : ℕ) 
  → ⦃ nonZero-r₁   : NonZero r₁ ⦄
  → ⦃ nonZero-r₂   : NonZero r₂ ⦄
  → 
            -ω 
              (r₂ *ₙ r₁) 
              ⦃ m*n≢0 r₂ r₁ ⦄
              (
                (r₂ *ₙ k₁ +ₙ k₀) 
                *ₙ 
                (r₁ *ₙ j₁ +ₙ j₀) 
              )
            ≡
              -ω (r₁) (k₁ *ₙ j₀) 
            * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
            * -ω (r₂) (k₀ *ₙ j₁)
cooley-tukey-derivation r₁ r₂ k₀ k₁ j₀ j₁ ⦃ nonZero-r₁ ⦄ ⦃ nonZero-r₂ ⦄
  = rearrange-ω-power 
  ⊡ split-ω
  ⊡ remove-constant-term
  ⊡ simplify-bases
  where
    instance
      _ : NonZero (r₁ *ₙ r₂)
      _ = m*n≢0 r₁ r₂
      _ : NonZero (r₂ *ₙ r₁)
      _ = m*n≢0 r₂ r₁ 
    simplify-bases :
          -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₂ *ₙ (k₁ *ₙ j₀)) 
        * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
        * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₁ *ₙ (k₀ *ₙ j₁))
      ≡
          -ω (r₁) (k₁ *ₙ j₀) 
        * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
        * -ω (r₂) (k₀ *ₙ j₁)
    simplify-bases = 
        cong₂ 
          _*_ 
          ( cong₂
                _*_
                (ω-r₁x-r₁y r₂ r₁ (k₁ *ₙ j₀))
                refl
          )
          (   -ω-cong₂ (*ₙ-comm r₂ r₁) refl
            ⊡ (ω-r₁x-r₁y r₁ r₂ (k₀ *ₙ j₁))
          )
    remove-constant-term :
          -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₂ *ₙ (k₁ *ₙ j₀)) 
        * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
        * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₁ *ₙ (k₀ *ₙ j₁))
        * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ ((r₂ *ₙ r₁) *ₙ (j₁ *ₙ k₁))
      ≡
          -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₂ *ₙ (k₁ *ₙ j₀)) 
        * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
        * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₁ *ₙ (k₀ *ₙ j₁))
    remove-constant-term =
        cong₂ _*_ refl (ω-N-mN {r₂ *ₙ r₁} {j₁ *ₙ k₁})
      ⊡ *-identityʳ _
    rearrange-ω-power :
        -ω 
          (r₂ *ₙ r₁) 
          (  (r₂ *ₙ k₁ +ₙ k₀) 
          *ₙ (r₁ *ₙ j₁ +ₙ j₀) 
          )
      
      ≡ 
        -ω 
          (r₂ *ₙ r₁)
          ( r₂ *ₙ (k₁ *ₙ j₀) 
          +ₙ k₀ *ₙ j₀ 
          +ₙ r₁ *ₙ (k₀ *ₙ j₁) 
          +ₙ r₂ *ₙ (r₁ *ₙ (j₁ *ₙ k₁))
          )
    rearrange-ω-power = 
      -ω-cong₂ 
        refl 
        (solve 
          6 
          (λ r₁ℕ r₂ℕ k₀ℕ k₁ℕ j₀ℕ j₁ℕ → (r₂ℕ :* k₁ℕ :+ k₀ℕ) :* (r₁ℕ :* j₁ℕ :+ j₀ℕ) := r₂ℕ :* (k₁ℕ :* j₀ℕ) :+ k₀ℕ :* j₀ℕ :+ r₁ℕ :* (k₀ℕ :* j₁ℕ) :+ r₂ℕ :* (r₁ℕ :* (j₁ℕ :* k₁ℕ))) 
          refl 
          r₁ r₂ k₀ k₁ j₀ j₁
        )
    split-ω :
        -ω 
          (r₂ *ₙ r₁)
          ( r₂ *ₙ (k₁ *ₙ j₀) 
          +ₙ k₀ *ₙ j₀ 
          +ₙ r₁ *ₙ (k₀ *ₙ j₁) 
          +ₙ r₂ *ₙ (r₁ *ₙ (j₁ *ₙ k₁))
          )
        ≡
          -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₂ *ₙ (k₁ *ₙ j₀)) 
        * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (k₀ *ₙ j₀) 
        * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ (r₁ *ₙ (k₀ *ₙ j₁))
        * -ω (r₂ *ₙ r₁) ⦃ m*n≢0 r₂ r₁ ⦄ ((r₂ *ₙ r₁) *ₙ (j₁ *ₙ k₁))
    split-ω = 
          (ω-N-k₀+k₁ {r₂ *ₙ r₁} {r₂ *ₙ (k₁ *ₙ j₀) +ₙ k₀ *ₙ j₀ +ₙ r₁ *ₙ (k₀ *ₙ j₁)} {r₂ *ₙ (r₁ *ₙ (j₁ *ₙ k₁))} )
        ⊡ (flip $ cong₂ _*_) (-ω-cong₂ refl $ sym $ *ₙ-assoc r₂ r₁ (j₁ *ₙ k₁)) 
        ( (ω-N-k₀+k₁ {r₂ *ₙ r₁} {r₂ *ₙ (k₁ *ₙ j₀) +ₙ k₀ *ₙ j₀                    } {r₁ *ₙ (k₀ *ₙ j₁)        } )
        ⊡ (flip $ cong₂ _*_) refl 
          (ω-N-k₀+k₁ {r₂ *ₙ r₁} {r₂ *ₙ (k₁ *ₙ j₀)                                } {k₀ *ₙ j₀                } )
        )

cooley-tukey-derivation-application : ∀
   (j₁   : Position (r₂ ᵗ))
   (j₀   : Position (r₁ ᵗ))
   (k₀   : Position (ι (# r₂ ᵗ)))
   (k₁   : Position (ι (# r₁ ᵗ)))
   → (nz-r₁ : NonZeroₛ r₁)
   → (nz-r₂ : NonZeroₛ r₂)
   → 
        -ω 
          (# r₁ ᵗ) 
          ⦃ nz-# (nzᵗ nz-r₁) ⦄
          (iota k₁ *ₙ iota (j₀ ⟨ rev ♭ ⟩)) 
      * -ω 
          (# r₂ *ₙ # r₁ ᵗ)
          ⦃ m*n≢0 (# r₂) (# r₁ ᵗ) ⦃ nz-# nz-r₂ ⦄ ⦃ nz-# (nzᵗ nz-r₁) ⦄ ⦄
          (iota (((k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩) ⟨ ♭ ⟩) ⟨ rev (♭ {r₂}) ⟩) *ₙ iota (j₀ ⟨ rev ♭ ⟩)) 
      * -ω 
          (# r₂ ᵗ) 
          ⦃ nz-# (nzᵗ nz-r₂) ⦄
          (iota k₀ *ₙ iota (j₁ ⟨ rev ♭ ⟩))
      ≡
        -ω 
          (# r₂ ᵗ *ₙ # r₁ ᵗ)
          ⦃ m*n≢0 (# r₂ ᵗ) (# r₁ ᵗ) ⦃ nz-# (nzᵗ nz-r₂) ⦄ ⦃ nz-# (nzᵗ nz-r₁) ⦄ ⦄
          (iota (((k₁ ⟨ reindex (|s|≡|sᵗ| {r₁}) ⟩) ⊗ (k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩)) ⟨ split ⟩) *ₙ iota (((j₁ ⟨ rev ♭ ⟩) ⊗ (j₀ ⟨ rev ♭ ⟩)) ⟨ split ⟩))
cooley-tukey-derivation-application {r₂} {r₁} j₁ j₀ k₀ k₁ nz-r₁ nz-r₂ =
  let instance
    _ : NonZero (# r₁)
    _ = nz-# nz-r₁
    _ : NonZero (# r₂)
    _ = nz-# nz-r₂
    _ : NonZero (# r₁ ᵗ)
    _ = nz-# (nzᵗ nz-r₁)
    _ : NonZero (# r₂ ᵗ)
    _ = nz-# (nzᵗ nz-r₂)
    _ : NonZero (# r₂ *ₙ # r₁ ᵗ)
    _ = m*n≢0 (# r₂) (# r₁ ᵗ)
    _ : NonZero (# r₂ ᵗ *ₙ # r₁ ᵗ)
    _ = m*n≢0 (# r₂ ᵗ) (# r₁ ᵗ)
  in begin
  _ ≡⟨  cong₂ _*_ 
          ( cong₂ _*_ 
              refl 
              ( -ω-cong₂ 
                  ( cong₂ _*ₙ_ (|s|≡|sᵗ| {r₂}) refl) 
                  ( cong₂ _*ₙ_ 
                      ( (cong 
                            iota 
                            (rev-eq {r₂} ♭ (k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩))
                        ) 
                      ⊡ (iota-reindex (|s|≡|sᵗ| {r₂}))
                      )
                      refl
                  )
              )
          ) 
          refl 
    ⟩
  _ ≡⟨ sym (cooley-tukey-derivation
        (# r₁ ᵗ) 
        (# r₂ ᵗ) 
        (iota k₀) 
        (iota k₁) 
        (iota (j₀ ⟨ rev ♭ ⟩)) 
        (iota (j₁ ⟨ rev ♭ ⟩)) 
       )
     ⟩
  _ ≡⟨ sym (-ω-cong₂ refl 
          (cong (_*ₙ (# r₁ ᵗ *ₙ iota (j₁ ⟨ rev ♭ ⟩) +ₙ iota (j₀ ⟨ rev ♭ ⟩))) 
            (cong ((# r₂ ᵗ *ₙ iota k₁ +ₙ_))
              (iota-reindex (|s|≡|sᵗ| {r₂}))
            )
          )
         ) 
   ⟩
  _ ≡⟨ sym (-ω-cong₂ refl 
          (cong (_*ₙ (# r₁ ᵗ *ₙ iota (j₁ ⟨ rev ♭ ⟩) +ₙ iota (j₀ ⟨ rev ♭ ⟩))) 
            (cong (_+ₙ iota (k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩)) 
              (cong (# r₂ ᵗ *ₙ_) (iota-reindex {# r₁ ᵗ} {# r₁} {k₁} (|s|≡|sᵗ| {r₁})))
            )
          )
         ) 
   ⟩
  _ ≡⟨ sym (-ω-cong₂ refl (cong₂ _*ₙ_ (cong₂ _+ₙ_ (cong₂ _*ₙ_ (|s|≡|sᵗ| {r₂}) refl) refl) refl)) ⟩
  _ ≡⟨ sym (-ω-cong₂ refl 
              (cong₂ _*ₙ_ 
                  (iota-split 
                    {r₂} 
                    {r₁} 
                    (k₀ ⟨ reindex (|s|≡|sᵗ| {r₂}) ⟩) 
                    (k₁ ⟨ reindex (|s|≡|sᵗ| {r₁}) ⟩)
                  ) 
                  (iota-split 
                    {ι (# r₁ ᵗ)} 
                    {ι (# r₂ ᵗ)} 
                    (j₀ ⟨ rev ♭ ⟩) 
                    (j₁ ⟨ rev ♭ ⟩)
                  )
              )
            ) 
      ⟩ 
  _ ∎
  
-----------------
--- FFT ≡ DFT ---
-----------------

destructDFT : (nz : NonZero N)
            → ∀ (xs : Ar (ι N) ℂ) 
            → ∀ i 
            → DFT xs i ≡ sum (λ k → xs k * -ω N ⦃ nz ⦄ (iota k *ₙ iota i))
destructDFT {N} nz-N _ _ with nonZero? N
... | no ¬nz-N = ⊥-elim (¬nz-N nz-N)
... | yes _ = refl

fft≅dft : 
    ∀ (arr : Ar s ℂ) 
  → FFT arr 
    ≅ 
    ( (reshape ♯) 
    ∘ DFT
    ∘ (reshape flatten-reindex)) arr
fft≅dft {ι n} _ (ι _) with nonZero? n 
... | _ = refl
fft≅dft {r₁ ⊗ r₂} arr (j₁ ⊗ j₀) with 
    nonZeroDec r₁ 
  | nonZeroDec r₂ 
  | nonZeroDec (recursive-transpose r₁) 
  | nonZeroDec (recursive-transpose r₂) 
  | nonZero? (length (recursive-transpose r₁)) 
  | nonZero? (length (recursive-transpose r₂))
... | no ¬nz-r₁ | _         | _          | _          | _           | _           = ⊥-elim (¬nz-r₁ (pos⇒nz (j₀ ⟨ recursive-transposeᵣ ⟩)))
... | yes nz-r₁ | no ¬nz-r₂ | _          | _          | _           | _           = ⊥-elim (¬nz-r₂ (pos⇒nz (j₁ ⟨ recursive-transposeᵣ ⟩)))
... | yes nz-r₁ | yes nz-r₂ | no ¬nz-r₁ᵗ | _          | _           | _           = ⊥-elim (¬nz-r₁ᵗ (pos⇒nz j₀))
... | yes nz-r₁ | yes nz-r₂ | yes nz-r₁ᵗ | no ¬nz-r₂ᵗ | _           | _           = ⊥-elim (¬nz-r₂ᵗ (pos⇒nz j₁))
... | yes nz-r₁ | yes nz-r₂ | yes nz-r₁ᵗ | yes nz-r₂ᵗ | no ¬nz-#r₁ᵗ | _           = ⊥-elim (¬nz-#r₁ᵗ (nonZeroₛ-s⇒nonZero-s nz-r₁ᵗ))
... | yes nz-r₁ | yes nz-r₂ | yes nz-r₁ᵗ | yes nz-r₂ᵗ | yes nz-#r₁ᵗ | no ¬nz-#r₂ᵗ = ⊥-elim (¬nz-#r₂ᵗ (nonZeroₛ-s⇒nonZero-s nz-r₂ᵗ))
... | yes nz-r₁ | yes nz-r₂ | yes nz-r₁ᵗ | yes nz-r₂ᵗ | yes nz-#r₁ᵗ | yes nz-#r₂ᵗ
  = 
  begin
    _ ≡⟨ fft≅dft _ j₁ ⟩
    _ ≡⟨ DFT-cong (λ x → cong₂ _*_ (fft≅dft _ j₀) refl) (j₁ ⟨ rev ♭ ⟩ ) ⟩
    _ ≡⟨ destructDFT nz-#r₂ᵗ _ _ ⟩
    _ ≡⟨ sum-cong { # r₂ ᵗ } (λ i → cong₂ _*_ (cong₂ _*_ (destructDFT nz-#r₁ᵗ _ _) refl) refl) ⟩
    _ ≡⟨  sum-cong {  # r₂ ᵗ } 
            (λ k₀ → 
                cong₂ _*_ (*-distribʳ-sum {# r₁ ᵗ} _) refl
              ⊡ *-distribʳ-sum {# r₁ ᵗ} _
              ⊡ sum-cong {# r₁ ᵗ }
                  (λ k₁ → 
                      assoc₄ _ _ _ _ 
                    ⊡ cong₂ _*_ 
                        (sym ((rev-eq-applied split (reshape (♭ ⊕ ♭) arr)) (_ ⊗ _))) 
                        refl
                  )
            )
        ⟩
    _ ≡⟨  sum-cong {  # r₂ ᵗ } (λ k₀ → 
            sum-cong {# r₁ ᵗ } (λ k₁ → 
              cong₂ _*_ refl
                (cooley-tukey-derivation-application j₁ j₀ k₀ k₁ nz-r₁ nz-r₂)
            )
          )
        ⟩
    _ ≡⟨  sum-cong {# r₂ ᵗ} (λ k₀ → sym (sum-reindex (|s|≡|sᵗ| {r₁})))
        ⊡ sym (sum-reindex (|s|≡|sᵗ| {r₂})) 
       ⟩
    _ ≡⟨  sum-swap {# r₂} {# r₁} _ 
        ⊡ merge-sum {# r₁} {# r₂} _
       ⟩
          sum { # (r₁ ⊗ r₂) }
            (λ k →
                 arr (((k) ⟨ flat ⟩) ⟨ ♭ ⊕ ♭ ⟩)
               *
                 -ω
                   (# r₂ ᵗ *ₙ # r₁ ᵗ)
                    ⦃ m*n≢0 _ _ ⦃ nz-#r₂ᵗ ⦄ ⦃ nz-#r₁ᵗ ⦄ ⦄
                   (iota k *ₙ iota (((j₁ ⟨ rev ♭ ⟩) ⊗ (j₀ ⟨ rev ♭ ⟩)) ⟨ split ⟩))
            )
      ≡⟨ sum-reindex (|s|≡|sᵗ| {r₁ ⊗ r₂}) ⟩
    _ ≡⟨ sum-cong 
        {# (r₁ ⊗ r₂) ᵗ} 
        (λ k → 
            cong₂ _*_ 
              refl 
              (-ω-cong₂ 
                ⦃ m*n≢0 _ _ ⦃ nz-#r₂ᵗ ⦄ ⦃ nz-#r₁ᵗ ⦄ ⦄
                ⦃ m*n≢0 _ _ ⦃ nz-#r₂ᵗ ⦄ ⦃ nz-#r₁ᵗ ⦄ ⦄
                refl 
                (cong₂ _*ₙ_ (iota-reindex (|s|≡|sᵗ| {r₁ ⊗ r₂})) refl)
              )
        ) 
      ⟩
    _ ≡⟨ sym (destructDFT (m*n≢0 _ _ ⦃ nz-#r₂ᵗ ⦄ ⦃ nz-#r₁ᵗ ⦄) _ _) ⟩
    _ ∎

{-
twiddles′ :  Ar (s ⊗ p) ℂ
twiddles′ {s} {p} i with nonZeroDec (s ⊗ p)
... | no ¬nz = ⊥-elim (zs-nopos ¬nz i)
... | yes nz = -ω (length (s ⊗ p)) ⦃ nonZeroₛ-s⇒nonZero-s nz ⦄ (offset-prod i)

dft : ∀ {n} → Ar (ι n) ℂ → Ar (ι n) ℂ
dft {n} xs with nonZero? n
... | no ¬nz = λ { (ι j) → ⊥-elim (¬nz (fin-nz _ j)) }
... | yes nz = λ j → sum (λ k → xs k * -ω n ⦃ nz ⦄ (iota k *ₙ iota j))


-- Original FFT
fft : ∀ {s : Shape} → Ar s ℂ → Ar (recursive-transpose s) ℂ
fft {ι n} = dft
fft {s ⊗ p} a = let
                  b = mapLeft fft (reshape swap a)  
                  c = zipWith _*_ b twiddles′
                  d  = mapLeft fft (reshape swap c)
                in reshape swap d

-- XXX: Here is where we compute twiddles differently!
postoffset-prod : Position (s ⊗ p) → ℕ
postoffset-prod (k ⊗ j) = iota (k ⟨ ♯ ⟩) *ₙ iota (j ⟨ rev recursive-transposeᵣ ∙ ♯ ⟩)
--                                                   ^
--                                                   |
--                                                   +---- HERE
preoffset-prod : Position (s ⊗ p) → ℕ
preoffset-prod (k ⊗ j) = iota (k ⟨ rev recursive-transposeᵣ ∙ ♯ ⟩) *ₙ iota (j ⟨ ♯ ⟩)

posttwiddles′ :  Ar (s ⊗ p) ℂ
posttwiddles′ {s} {p} i with nonZeroDec (s ⊗ p)
... | no ¬nz = ⊥-elim (zs-nopos ¬nz i)
... | yes nz = -ω (length (s ⊗ p)) ⦃ nonZeroₛ-s⇒nonZero-s nz ⦄ (postoffset-prod i)

pretwiddles′ :  Ar (s ⊗ p) ℂ
pretwiddles′ {s} {p} i with nonZeroDec (s ⊗ p)
... | no ¬nz = ⊥-elim (zs-nopos ¬nz i)
... | yes nz = -ω (length (s ⊗ p)) ⦃ nonZeroₛ-s⇒nonZero-s nz ⦄ (preoffset-prod i)

-- FFT that does not swap dimensions
postfft : ∀ {s : Shape} → Ar s ℂ → Ar s ℂ
postfft {ι n} = dft
postfft {s ⊗ p} a = let
  b = mapLeft (postfft {s}) (reshape swap a)  
  c = zipWith _*_ b posttwiddles′
  d = mapLeft (postfft {p}) (reshape swap c)
  in d

prefft : ∀ {s : Shape} → Ar s ℂ → Ar s ℂ
prefft {ι n} = dft
prefft {s ⊗ p} a = let
  b = mapLeft (prefft {p}) a  
  c = zipWith _*_ b pretwiddles′ -- This may actually need to be post twiddles, will see how proof goes
  d = reshape swap (mapLeft (prefft {s}) (reshape swap c))
  in d

trans-helper : (i : Position (recursive-transpose s)) → ((i ⟨ recursive-transposeᵣ ⟩) ⟨ rev recursive-transposeᵣ ⟩) ≡ i
trans-helper {ι n} (ι i) = refl
trans-helper {s ⊗ s₁} (i ⊗ i₁) rewrite
    trans-helper i 
  | trans-helper i₁ = refl

-- TODO: This does hold... move proof over from parm
postulate 
  helper : ∀ {s} → ∀ j → iota (_⟨_⟩ {s} j (rev ♭) ) ≡
                         iota (((j ⟨ rev recursive-transposeᵣ ⟩) ⟨ rev recursive-transposeᵣ ⟩) ⟨ rev ♭ ⟩)

twid-posttwid : (i : Position s) (j : Position (recursive-transpose p))
             → twiddles′ (i ⊗ j) ≡ posttwiddles′ (i ⊗ (j ⟨ recursive-transposeᵣ ⟩))
twid-posttwid {s}{p} i j  with nonZeroDec (s ⊗ recursive-transpose p)
... | no ¬nzspt = ⊥-elim (¬nzspt (pos⇒nz (i ⊗ j)))
... | yes (nzs ⊗ nzpt) with nonZeroDec (s ⊗ p)
... | no ¬nzsp = ⊥-elim (¬nzsp (pos⇒nz (i ⊗ (j ⟨ rev recursive-transposeᵣ ∙ recursive-transpose-invᵣ ⟩))))
... | yes (nzs ⊗ nzp) rewrite trans-helper j = -ω-cong₂ (cong (length s *ₙ_) (sym (|s|≡|sᵗ| {p}))) refl 
  where
    instance
      _ : NonZero (length s *ₙ length (recursive-transpose p))
      _ = nonZeroₛ-s⇒nonZero-s (nzs ⊗ nzpt)
      _ : NonZero (length s *ₙ length p)
      _ = nonZeroₛ-s⇒nonZero-s (nzs ⊗ nzp)

twid-pretwid : (i : Position (recursive-transpose s)) (j : Position p)
             → twiddles′ (j ⊗ i) ≡ pretwiddles′ ((j ⟨ rev recursive-transposeᵣ ⟩) ⊗ i)
twid-pretwid {s}{p} i j  with nonZeroDec (p ⊗ recursive-transpose s )
... | no ¬nzstp = ⊥-elim (¬nzstp (pos⇒nz (j ⊗ i)))
... | yes (_ ⊗ nzst) with nonZeroDec (s ⊗ p)  | nonZeroDec (recursive-transpose p ⊗ recursive-transpose s)
... | no ¬nzsp | a = ⊥-elim (¬nzsp (pos⇒nz ((i ⟨ rev recursive-transposeᵣ ∙ recursive-transpose-invᵣ ⟩) ⊗ j)))
... | yes (nzs ⊗ nzp) | no ¬nzptst = ⊥-elim (¬nzptst ((nonZeroₛ-s⇒nonZeroₛ-sᵗ nzp) ⊗  nzst ))
... | yes (nzs ⊗ nzp) | yes a rewrite helper j = -ω-cong₂ (cong (_*ₙ length (recursive-transpose s)) ((|s|≡|sᵗ| {p}))) refl
--... | yes (nzs ⊗ nzp) | a rewrite trans-helper i = ? -- -ω-cong₂ (cong (_*ₙ length p) (sym (|s|≡|sᵗ| {s}))) refl 
  where
    instance
      _ : NonZero (length (recursive-transpose p) *ₙ length (recursive-transpose s))
      _ = nonZeroₛ-s⇒nonZero-s (a) 
      _ : NonZero (length p *ₙ length (recursive-transpose s))
      _ = nonZeroₛ-s⇒nonZero-s (nzp ⊗ nzst)  



dft-cong : ∀ {xs ys : Ar (ι N) ℂ} → ⦃ nonZero-N : NonZero N ⦄ → xs ≅ ys → dft xs ≅ dft ys
dft-cong {suc N} ⦃ nonZero-N ⦄ prf (ι j) = sum-cong {suc N} (λ i → cong₂ _*_ (prf i) refl)

-- Prove that fft a ~ trans (postfft a)
trans-after : (a b : Ar s ℂ) → (∀ i → a i ≡ b i) → ∀ i → fft a i ≡ reshape recursive-transposeᵣ (postfft b) i
trans-after {ι zero} a b e (ι ())
trans-after {ι (suc x)} a b e i with dft-cong e 
... | tm = tm i
trans-after {s ⊗ s₁} a b e (i ⊗ i₁) = trans-after _ _ (λ j → Eq.cong₂ _*_ (trans-after _ _ (λ i₂ → e ((j ⊗ i₂) ⟨ swap ⟩)) i₁) (twid-posttwid {s₁} {s} j _)) i


trans-before :  (a : Ar s ℂ) 
              → (b : Ar _ ℂ) 
              → (∀ i → a i ≡ b (i ⟨ rev recursive-transposeᵣ ⟩)) 
              → ∀ i 
              → fft a i ≡ prefft b i
trans-before {ι zero} a b e (ι ())
trans-before {ι (suc x)} a b e i with dft-cong e
... | tm = tm i
trans-before {s ⊗ s₁} a b e (i₁ ⊗ i₂) = 
      trans-before _ _ (λ j₁ → Eq.cong₂ _*_ (trans-before _ _ (λ j₂ → e (j₂ ⊗ j₁)) i₂) (twid-pretwid _ j₁)) i₁



-}





