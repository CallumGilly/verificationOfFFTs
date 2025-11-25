open import Real using (Real)
open import Complex using (Cplx)

import Algebra.Structures as AlgebraStructures
import Algebra.Definitions as AlgebraDefinitions

open import Relation.Nullary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; sym; cong₂; subst; cong-app; cong′; icong)
open Eq.≡-Reasoning

module Proof (cplx : Cplx) where

open Cplx cplx using (ℂ; _+_; _*_; -ω; 0ℂ; +-*-isCommutativeRing; ω-r₁x-r₁y; ω-N-mN; ω-N-k₀+k₁)

open AlgebraStructures  {A = ℂ} _≡_
open AlgebraDefinitions {A = ℂ} _≡_

open IsCommutativeRing +-*-isCommutativeRing using (+-isCommutativeMonoid; distribˡ; *-comm; zeroʳ; zeroˡ; *-identityʳ; *-assoc; +-identityʳ; +-assoc; +-comm; +-identityˡ)

open import Data.Nat.Base using (ℕ; zero; suc; NonZero; _≡ᵇ_; nonZero) renaming (_*_ to _*ₙ_; _+_ to _+ₙ_)
open import Data.Nat.Properties using (suc-injective; m*n≢0; m*n≢0⇒m≢0; m*n≢0⇒n≢0; nonZero?) renaming (*-comm to *ₙ-comm; *-identityʳ to *ₙ-identityʳ; *-assoc to *ₙ-assoc; 
  +-identityʳ to +ₙ-identityʳ; *-zeroˡ to *ₙ-zeroˡ; *-zeroʳ to *ₙ-zeroʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
open import Data.Fin.Base using (Fin; quotRem; toℕ; combine; remQuot; quotient; remainder; cast; fromℕ<; _↑ˡ_; _↑ʳ_; splitAt; join) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (cast-is-id; remQuot-combine; splitAt-↑ˡ; splitAt-↑ʳ; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-combine; combine-remQuot; combine-surjective; toℕ-injective; toℕ-cast; cast-trans)
open import Data.Bool using (Bool; true; false; not)
open import Data.Bool using (T)
open import Data.Empty

open import Data.Product.Base using (∃; ∃₂; _×_; proj₁; proj₂; map₁; map₂; uncurry) renaming ( _,_ to ⟨_,_⟩)
open import Data.Sum.Base using (inj₁; inj₂; _⊎_)
open import Data.Unit using (⊤; tt)

open import Matrix using (Ar; Shape; _⊗_; ι; Position; mapLeft; zipWith; nest; map; unnest; head₁; tail₁; zip; iterate; ι-cons; nil; length; splitAr; splitArₗ; splitArᵣ)
open import Matrix.Equality using (_≅_; reduce-≅; tail₁-cong)
open import Matrix.Properties using (splitArᵣ-zero; tail₁-const; zipWith-congˡ)
open import Matrix.NonZero using (NonZeroₛ; ι; _⊗_; nonZeroₛ-s⇒nonZero-s; nonZeroDec; nonZeroₛ-s⇒nonZeroₛ-sᵗ; nonZeroₛ-s⇒nonZero-sᵗ; ¬nonZeroₛ-s⇒¬nonZero-sᵗ; ¬nonZero-N⇒PosN-irrelevant; ¬nonZero-sᵗ⇒¬nonZero-s)

import Matrix.Sum as S
open S _+_ 0ℂ +-isCommutativeMonoid using (merge-sum; sum-reindex; sum-swap)
sum = S.sum _+_ 0ℂ +-isCommutativeMonoid
{-# DISPLAY S.sum _+_ 0ℂ +-isCommutativeMonoid = sum #-}
sum-cong = S.sum-cong _+_ 0ℂ +-isCommutativeMonoid

open import Matrix.Reshape using (reshape; Reshape; flat; ♭; ♯; recursive-transpose; recursive-transposeᵣ; _∙_; rev; _⊕_; swap; eq; split; _⟨_⟩; reindex; rev-eq; flatten-reindex; |s|≡|sᵗ|; reindex-reindex; recursive-transpose-inv)
open import Function.Base using (_$_; id; _∘_; flip; _∘₂_)

open import FFT cplx using (DFT; FFT; DFT′; FFT′; FFT′′; offset-prod; iota; twiddles)

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

nz-ι# : NonZeroₛ s → NonZeroₛ (ι (length s))
nz-ι# (ι x) = ι x
nz-ι# {s ⊗ p} (nz-s ⊗ nz-p) = ι (m*n≢0 (# s) (# p) ⦃ nz-# nz-s ⦄ ⦃ nz-# nz-p ⦄ )

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

DFT′-cong : ∀ {xs ys : Ar (ι N) ℂ} → ⦃ nonZero-N : NonZero N ⦄ → xs ≅ ys → DFT′ xs ≅ DFT′ ys
DFT′-cong {suc N} ⦃ nonZero-N ⦄ prf (ι j) = sum-cong {suc N} (λ i → cong₂ _*_ (prf i) refl)

FFT′-cong : ∀ {s : Shape} {xs ys : Ar s ℂ} → ⦃ nonZeroₛ-s : NonZeroₛ s ⦄ → xs ≅ ys → FFT′ xs ≅ FFT′ ys
FFT′-cong {ι N} ⦃ ι nonZero-N ⦄ = DFT′-cong ⦃ nonZero-N ⦄
FFT′-cong {r₁ ⊗ r₂} {xs} {ys} ⦃ nonZero-r₁ ⊗ nonZero-r₂ ⦄ prf (j₁ ⊗ j₀) =
  let instance
    _ : NonZeroₛ r₁
    _ = nonZero-r₁
    _ : NonZeroₛ r₂
    _ = nonZero-r₂
  in  (FFT′-cong {r₂} λ{ k₀ → 
        (cong₂ _*_ 
          ((FFT′-cong {r₁} λ{k₁ → 
            prf (k₁ ⊗ k₀) 
          }) j₀ ) 
          refl
        ) 
      }) j₁

reshape-cong : ∀ {s p : Shape} {xs ys : Ar s ℂ} → (r : Reshape s p) → xs ≅ ys → reshape r xs ≅ reshape r ys
reshape-cong r x i = x ( i ⟨ r ⟩ ) 
  

{-
--postulate
FFT′′-cong : ∀ {s : Shape} {xs ys : Ar s ℂ} → ⦃ nonZeroₛ-s : NonZeroₛ s ⦄ → xs ≅ ys → FFT′′ xs ≅ FFT′′ ys
FFT′′-cong {ι N} ⦃ ι nonZero-N ⦄ = DFT′-cong ⦃ nonZero-N ⦄
FFT′′-cong {r₁ ⊗ r₂} {xs} {ys} ⦃ nonZero-r₁ ⊗ nonZero-r₂ ⦄ prf (j₀ ⊗ j₁) =
  let instance
    _ : NonZeroₛ r₁
    _ = nonZero-r₁
    _ : NonZeroₛ r₂
    _ = nonZero-r₂
    _ : NonZeroₛ (r₁ ⊗ r₂)
    _ = nonZero-r₁ ⊗ nonZero-r₂
  in begin 
    FFT′′ xs (j₀ ⊗ j₁)
  --≡⟨ ? ⟩ 
  ≡⟨ (reshape-cong (♯ ∙ reindex (*ₙ-comm (length r₂) (length r₁)) ∙ (flat ∙ ♭ ⊕ ♭) ∙ swap) (FFT′′-cong {?} ⦃ ? ⦄ ?)) (j₀ ⊗ j₁) ⟩ 
  --≡⟨ cong (λ f → reshape (♯ ∙ reindex (*ₙ-comm (length r₂) (length r₁)) ∙ (flat ∙ ♭ ⊕ ♭) ∙ swap) f (j₀ ⊗ j₁)) ? ⟩
    ?
  ≡⟨ ? ⟩
    FFT′′ ys (j₀ ⊗ j₁)
  ∎
  -}

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

fft′≅dft′ : 
    ⦃ nz-s  : NonZeroₛ s ⦄
  → ∀ (arr : Ar s ℂ) 
  → FFT′ arr 
    ≅ 
    ( (reshape ♯) 
    ∘ (DFT′ ⦃ nz-# (nzᵗ nz-s) ⦄ )
    ∘ (reshape flatten-reindex)) arr
fft′≅dft′ {ι N} ⦃ ι nz-N ⦄ arr i = refl
fft′≅dft′ {r₁ ⊗ r₂} ⦃ nz-r₁ ⊗ nz-r₂ ⦄ arr (j₁ ⊗ j₀) =
  let instance
    _ : NonZeroₛ r₁
    _ = nz-r₁
    _ : NonZeroₛ r₂
    _ = nz-r₂
    _ : NonZero (# r₁)
    _ = (nz-# nz-r₁)
    _ : NonZero (# r₂)
    _ = (nz-# nz-r₂)
    _ : NonZero (# r₁ ᵗ)
    _ = (nz-# (nzᵗ nz-r₁))
    _ : NonZero (# r₂ ᵗ)
    _ = (nz-# (nzᵗ nz-r₂))
    _ : NonZero (# r₂   *ₙ # r₁ ᵗ)
    _ = m*n≢0 (# r₂) (# r₁ ᵗ)
    _ : NonZero (# r₂ ᵗ *ₙ # r₁ ᵗ)
    _ = m*n≢0 (# r₂ ᵗ) (# r₁ ᵗ)
  in begin
    _ ≡⟨ fft′≅dft′ _ j₁ ⟩
    _ ≡⟨ DFT′-cong (λ x → cong₂ _*_ (fft′≅dft′ _ j₀) refl) (j₁ ⟨ rev ♭ ⟩ ) ⟩
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
                   (iota k *ₙ iota (((j₁ ⟨ rev ♭ ⟩) ⊗ (j₀ ⟨ rev ♭ ⟩)) ⟨ split ⟩))
            )
      ≡⟨ sum-reindex (|s|≡|sᵗ| {r₁ ⊗ r₂}) ⟩
        sum {# (r₁ ⊗ r₂) ᵗ} _
      ≡⟨ sum-cong 
        {# (r₁ ⊗ r₂) ᵗ} 
        (λ k → 
            cong₂ _*_ 
              refl 
              (-ω-cong₂ 
                refl 
                (cong₂ _*ₙ_ (iota-reindex (|s|≡|sᵗ| {r₁ ⊗ r₂})) refl)
              )
        ) 
      ⟩
      (reshape ♯ ∘ (DFT′ {length (recursive-transpose (r₁ ⊗ r₂))}) ∘ reshape flatten-reindex) arr (j₁ ⊗ j₀)
    ∎

fft≅dft : 
    ∀ (arr : Ar s ℂ) 
  → FFT arr 
    ≅ 
    ( (reshape ♯) 
    ∘ DFT
    ∘ (reshape flatten-reindex)) arr
fft≅dft {s} arr i with nonZeroDec s | nonZero? (# s ᵗ) 
fft≅dft {s} arr i | yes  nz-s | yes  nz-#sᵗ = fft′≅dft′ ⦃ nz-s ⦄ arr i
fft≅dft {s} arr i | yes  nz-s | no  ¬nz-#sᵗ = ⊥-elim (¬nz-#sᵗ (nonZeroₛ-s⇒nonZero-sᵗ {s} nz-s))
fft≅dft {s} arr i | no  ¬nz-s | yes  nz-#sᵗ = ⊥-elim ((¬nonZeroₛ-s⇒¬nonZero-sᵗ ¬nz-s) nz-#sᵗ)
fft≅dft {s} arr i | no  ¬nz-s | no  ¬nz-#sᵗ 
  with (i ⟨ recursive-transposeᵣ ⟩) | (((i ⟨ rev ♭ ⟩) ⟨ reindex (|s|≡|sᵗ| {s}) ⟩) ⟨ ♭ {s} ⟩)
fft≅dft {s} arr i | no ¬nz-s  | no ¬nz-#sᵗ  | p | j = 
  cong arr 
    $ (sym (rev-eq ♯ p)) 
    ⊡ (cong _⟨ rev ♯ ⟩ (¬nonZero-N⇒PosN-irrelevant (¬nonZero-sᵗ⇒¬nonZero-s {s} ¬nz-#sᵗ) (p ⟨ ♯ ⟩) (j ⟨ ♯ ⟩) ))
    ⊡ (rev-eq ♯ j)

